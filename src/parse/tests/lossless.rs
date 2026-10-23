use crate::driver::MAIN_MODULE;
use crate::error::{Diagnostic, DiagnosticManager, Error};
use crate::lexer::{FmtToken, TriviaKind};
use crate::parse::grammar::RESERVED_PATTERN_NAMES;
use crate::parse::{
    ExpressionInner, Item, ParseFromStrWithErrors, ParsedSource, Program, Visibility,
};
use crate::UnstableFeatures;

/// Parse `input`, appending any formatter diagnostics to `diagnostics`.
fn parse_with_diagnostics<'src>(
    input: &'src str,
    features: &UnstableFeatures,
    diagnostics: &mut DiagnosticManager,
) -> Option<ParsedSource<'src>> {
    Program::parse_with_errors_for_fmt(MAIN_MODULE, input, features, diagnostics)
}

/// Parse `input` and return whether it was rejected and the collected error text.
fn parse_with(input: &str, features: &UnstableFeatures) -> (bool, String) {
    let mut diagnostics = DiagnosticManager::new();
    let program = parse_with_diagnostics(input, features, &mut diagnostics);

    let rejected = program.is_none();
    let text = diagnostics.to_string();

    (rejected, text)
}

/// Parse `input` and return whether it was rejected and the collected error in `DiagnosticManager`.
fn parse_with_diagnosis(input: &str, features: &UnstableFeatures) -> (bool, DiagnosticManager) {
    let mut diagnostics = DiagnosticManager::new();
    let program = parse_with_diagnostics(input, features, &mut diagnostics);

    let rejected = program.is_none();

    (rejected, diagnostics)
}

/// Parse `input` and return whether it was rejected and the collected error text together with `ParsedSource`.
fn parse_with_extended_out<'src>(
    input: &'src str,
    features: &UnstableFeatures,
) -> (bool, String, Option<ParsedSource<'src>>) {
    let mut diagnostics = DiagnosticManager::new();
    let program = parse_with_diagnostics(input, features, &mut diagnostics);

    let rejected = program.is_none();
    let text = diagnostics.to_string();

    (rejected, text, program)
}

fn assert_formatter_matches_regular_parser(input: &str, features: &UnstableFeatures) {
    let mut regular_diagnostics = DiagnosticManager::new();
    let regular =
        Program::parse_from_str_with_errors(MAIN_MODULE, input, features, &mut regular_diagnostics);

    let mut formatting_diagnostics = DiagnosticManager::new();
    let formatting = parse_with_diagnostics(input, features, &mut formatting_diagnostics);

    assert_eq!(
        formatting.as_ref().map(ParsedSource::program),
        regular.as_ref(),
        "formatter and regular parsers must produce the same AST for {input:?}"
    );
    assert_eq!(
                formatting_diagnostics.error_count(),
                regular_diagnostics.error_count(),
                "formatter and regular parsers must report the same number of errors for {input:?}, \n\
                 fmt errors: \n\t '{formatting_diagnostics}, \n regular errors: \n\t '{regular_diagnostics}"
            );
}

fn assert_lossless_source(input: &str, parsed: &ParsedSource<'_>) {
    let prefix = parsed.prefix();
    assert_eq!(prefix.file_id, MAIN_MODULE);

    let mut reconstructed = prefix
        .to_slice(input)
        .expect("the directive prefix must be a valid source slice")
        .to_owned();
    let mut cursor = prefix.end;

    for (_, span) in parsed.tokens() {
        assert_eq!(span.file_id, MAIN_MODULE);
        assert!(
            span.start >= prefix.end,
            "formatter tokens must not overlap the preserved directive prefix"
        );
        assert_eq!(
            span.start, cursor,
            "formatter token spans must be contiguous and in source order"
        );

        let text = span
            .to_slice(input)
            .expect("formatter token spans must be valid source slices");
        assert!(
            !text.is_empty(),
            "the formatter token stream must not contain empty source slices"
        );
        reconstructed.push_str(text);
        cursor = span.end;
    }

    assert_eq!(cursor, input.len(), "formatter tokens must reach EOF");
    assert_eq!(reconstructed, input, "formatter input must be lossless");
}

#[test]
fn test_double_colon() {
    let input = "fn main() { let ab: u8 = <(u4, u4)> : :into((0b1011, 0b1101)); }";

    let (rejected, text) = parse_with(input, &UnstableFeatures::all());

    assert!(rejected);
    assert!(text.contains("Expected '::', found ':'"));
}

#[test]
fn test_double_double_colon() {
    let input = "fn main() { let pk: Pubkey = witnes::::PK; }";

    let (rejected, text) = parse_with(input, &UnstableFeatures::all());

    assert!(rejected);
    assert!(
        text.contains("Expected identifier, found ::"),
        "the second :: should be reported as the error site"
    );
}

#[test]
fn inverted_empty_span_from_token_gap_does_not_panic() {
    // Fuzz-found (compile_text).
    //
    // The input is irreducible. The broken `fn` prefix forces the parser into delimiter recovery.
    // The only path that requests an empty span at a lex-error gap and the
    // NUL after `enum` creates that gap.
    // Chumsky builds such spans as `next_token.start .. previous_token.end`, which is inverted
    // across the gap and panicked the strict `Span` constructor.
    //
    // Simplifying any part (even NUL to a space) loses the crash.
    let src = "fn`u({?\u{12}$0;;enum\0===lHf\u{15}";
    let (rejected, text) = parse_with(src, &UnstableFeatures::all());

    assert!(rejected, "garbage input must be rejected");
    assert!(!text.is_empty());
}

#[test]
fn recovery_synchronizes_at_enum_declaration() {
    // Discriminating setup: an invalid prefix followed by a malformed
    // enum. Without `Token::Enum` in the synchronization set the whole
    // enum is swallowed into the prefix's recovery span and only one
    // error is reported; with it, the enum parses as its own item and
    // its malformation is reported as a second error.

    let src = "let invalid = 1;\nenum Action { A B }\nfn main() {}";
    let (rejected, diagnostics) = parse_with_diagnosis(src, &UnstableFeatures::all());

    assert!(rejected, "the invalid program must be rejected");
    assert_eq!(
        2,
        diagnostics.error_count(),
        "the invalid prefix and the malformed enum must each report an error"
    );
}

#[test]
fn recovery_after_malformed_enum_reaches_next_item() {
    let src = "enum Action { A B }\nfn main() {}";
    let (rejected, _text) = parse_with(src, &UnstableFeatures::all());
    assert!(rejected, "a malformed enum must fail compilation");
}

#[test]
fn malformed_construct_containing_enum_keyword_reports_errors() {
    // `enum` inside a badly malformed nested construct may be mistaken
    // for an item boundary; compilation must still fail cleanly.
    let src = "fn broken() { let x = (enum; }\nfn main() {}";
    let (rejected, _text) = parse_with(src, &UnstableFeatures::all());
    assert!(rejected, "a malformed construct must fail compilation");
}

#[test]
fn test_gated_syntax_is_rejected_without_features() {
    // Real `use`/`mod` syntax: rejected under none() (naming the feature + a
    // -Z hint), accepted under all(). Delete when `imports` stabilizes.
    for input in [
        "use crate::foo::bar;\nfn main() { }",
        "mod inner { }\nfn main() { }",
    ] {
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(
            rejected,
            "gated syntax must be rejected without features (if this feature was \
                 just stabilized, delete this test):\n{input}"
        );
        assert!(
            error.contains("imports") && error.contains("-Z"),
            "rejection should name the feature and suggest -Z, got:\n{error}"
        );

        let (rejected, error) = parse_with(input, &UnstableFeatures::all());
        assert!(
            !rejected,
            "the same syntax must parse with all features enabled:\n{error}"
        );
    }
}

#[test]
fn test_type_heavy_program_needs_no_features() {
    // Types are traversed by `RequireFeature` but not gated, so a type-heavy,
    // import-free program must parse with no features (no false-positive gates).
    let input = r#"type Alias = u32;
fn pick(e: Either<u32, u32>) -> u32 {
    match e {
        Left(a: u32) => a,
        Right(b: u32) => b,
    }
}
fn main() {
    let casted: u32 = <(u16, u16)>::into((0xbeef, 0xbabe));
    let chosen: Alias = pick(Left(casted));
    assert!(jet::eq_32(chosen, chosen));
}
"#;
    // `parse_from_str_with_errors` returns `Some` only when no errors were
    // collected, so a non-rejection already proves there were no gate errors.
    let (rejected, error) = parse_with(input, &UnstableFeatures::none());
    assert!(
        !rejected,
        "type-heavy but import-free program should parse with no features:\n{error}"
    );
}

#[test]
fn test_syntax_error_does_not_produce_spurious_feature_gate_error() {
    // The gate check skips error-recovered ASTs, so a program with
    // both a syntax error and gated syntax reports only the syntax error.
    let input = "use crate::foo;\nfn main( {";
    let (rejected, error) = parse_with(input, &UnstableFeatures::none());
    assert!(rejected, "broken program must be rejected");
    assert!(
        !error.contains("-Z"),
        "syntax error should not produce a spurious feature-gate hint, got:\n{error}"
    );
}

#[test]
fn test_lexer_error_does_not_produce_spurious_feature_gate_error() {
    // Lexer-side companion to the case above: the stray `@` lexes with an
    // error but recovers a cleanly-parsing `use` AST, and a program that
    // didn't lex cleanly skips the gate check — so no spurious `-Z` hint.
    let input = "use crate@::foo;\nfn main() { }";
    let (rejected, error) = parse_with(input, &UnstableFeatures::none());
    assert!(rejected, "program with a lexer error must be rejected");
    assert!(
        !error.contains("-Z"),
        "lexer error should not produce a spurious feature-gate hint, got:\n{error}"
    );
}

#[test]
fn test_use_decl_display_round_trips_with_aliases() {
    for input in [
        "use lib::A::foo;",
        "use lib::A::foo as bar;",
        "use lib::A::{foo, bar as baz};",
    ] {
        let (rejected, _, program) = parse_with_extended_out(input, &UnstableFeatures::all());
        assert!(!rejected, "parsing works");
        assert_eq!(program.unwrap().program().to_string(), format!("{input}\n"));
    }
}

#[test]
fn statement_spans_exclude_terminating_semicolons() {
    let input = "fn main() { let value: u8 = 0; value; }";

    let (rejected, _, program) = parse_with_extended_out(input, &UnstableFeatures::none());
    assert!(!rejected, "parsing works");
    let program = program.unwrap().program().clone();

    let Item::Function(function) = &program.items()[0] else {
        panic!("expected a function item");
    };
    let ExpressionInner::Block(statements, None) = function.body().inner() else {
        panic!("expected a block containing only statements");
    };

    assert_eq!(
        statements[0].span().to_slice(input),
        Some("let value: u8 = 0")
    );
    assert_eq!(statements[1].span().to_slice(input), Some("value"));
}

fn parse_item(input: &str) -> Item {
    let (rejected, _, program) = parse_with_extended_out(input, &UnstableFeatures::all());
    assert!(!rejected, "parsing works");
    let program = program.unwrap().program().clone();

    program.items().first().expect("expected one item").clone()
}

#[test]
fn test_enum_declaration_basic() {
    let item = parse_item("enum Path { Inherit, ColdSpend, RefreshSpend, }");
    let Item::EnumDeclaration(decl) = item else {
        panic!("expected EnumDeclaration, got {item:?}");
    };
    assert_eq!(decl.name(), "Path");
    assert_eq!(decl.variants().len(), 3);
    assert_eq!(decl.variants()[0].name(), "Inherit");
    assert_eq!(decl.variants()[2].name(), "RefreshSpend");
}

#[test]
fn test_enum_declaration_pub() {
    let item = parse_item("pub enum Color { Red, Green, Blue, }");
    let Item::EnumDeclaration(decl) = item else {
        panic!("expected EnumDeclaration");
    };
    assert_eq!(decl.visibility(), &Visibility::Public);
    assert_eq!(decl.name(), "Color");
}

#[test]
fn test_enum_declaration_display_round_trip() {
    let input = "enum Path { Inherit, ColdSpend, RefreshSpend, }";
    let item = parse_item(input);
    let Item::EnumDeclaration(decl) = item else {
        panic!("expected EnumDeclaration");
    };
    assert_eq!(
        decl.to_string(),
        "enum Path { Inherit, ColdSpend, RefreshSpend, }"
    );
}

#[test]
fn test_enum_declaration_reserved_name() {
    for reserved in RESERVED_PATTERN_NAMES {
        let input = format!("enum {reserved} {{ A, B, }}");
        let (rejected, error) = parse_with(&input, &UnstableFeatures::none());
        assert!(rejected, "enum name {reserved} is reserved");
        assert!(
            error.contains("reserved"),
            "error should say the name is reserved: {error}"
        );
    }
}

#[test]
fn formatting_parse_is_lossless_after_directive_prescan() {
    let input = "// header\r\nsimc \"*\";\r\n\t/* block */ fn main() { // body\r\n\t}\r";

    let (_rejected, _error, parsed) = parse_with_extended_out(input, &UnstableFeatures::none());
    let parsed = parsed.expect("formatting parse should succeed");

    assert_eq!(
        parsed.prefix().to_slice(input),
        Some("// header\r\nsimc \"*\";")
    );
    for trivia in [
        TriviaKind::BlockComment,
        TriviaKind::LineComment,
        TriviaKind::Newline,
        TriviaKind::Whitespace,
    ] {
        assert!(
                    parsed.tokens().iter().any(
                        |(token, _)| matches!(token, FmtToken::Trivia(token_trivia) if token_trivia.kind() == trivia)
                    ),
                    "formatter token stream should retain {trivia:?}"
                );
    }
    assert_lossless_source(input, &parsed);
    assert_eq!(parsed.program().items().len(), 1);
}

#[test]
fn formatting_parse_matches_regular_parser_pipeline() {
    let no_features = UnstableFeatures::none();
    let all_features = UnstableFeatures::all();

    for (input, features) in [
        (
            "/* header */\r\nfn\tmain() { // comment\r\n}\r",
            &no_features,
        ),
        ("// version\r\nsimc \"*\";\r\nfn main() {}", &no_features),
        ("use crate::foo::bar;\nfn main() {}", &no_features),
        ("use crate::foo::bar;\nfn main() {}", &all_features),
        ("fn main( {", &no_features),
        ("fn main() { @// comment }", &no_features),
    ] {
        assert_formatter_matches_regular_parser(input, features);
    }
}

#[test]
fn formatting_parse_ignores_preexisting_errors() {
    let input = "fn main() {}";
    let mut diagnostics = DiagnosticManager::new();
    diagnostics.push(Diagnostic::global(Error::CannotParse {
        msg: "an error from an earlier source file".to_owned(),
    }));
    let before = diagnostics.error_count();

    let parsed = parse_with_diagnostics(input, &UnstableFeatures::none(), &mut diagnostics);

    assert!(
        parsed.is_some(),
        "valid source must still produce ParsedSource"
    );
    assert_eq!(diagnostics.error_count(), before);
    assert_eq!(diagnostics.diagnostics().len(), before);
}

#[test]
fn formatting_parse_stops_after_invalid_directive() {
    for (input, is_malformed) in [
        ("simc \"*\"\nfn broken( @", true),
        ("simc \">99.0.0\"; @", false),
    ] {
        let (rejected, diagnostics) = parse_with_diagnosis(input, &UnstableFeatures::none());

        assert!(rejected, "invalid directive must abort formatting parse");
        assert_eq!(
            diagnostics.error_count(),
            1,
            "the invalid body must not add diagnostics after prescan aborts"
        );
        if is_malformed {
            assert!(matches!(
                diagnostics.diagnostics()[0].error(),
                Error::MalformedSimcDirective
            ));
        } else {
            assert!(matches!(
                diagnostics.diagnostics()[0].error(),
                Error::SimcVersionMismatch { .. }
            ));
        }
    }
}

#[test]
fn formatting_parse_reports_missing_match_arm_comma() {
    let input = "fn main() { match true { false => () true => (), } }";

    let (rejected, error) = parse_with(input, &UnstableFeatures::none());

    assert!(rejected);
    assert!(
        error.contains("Missing ',' after a match arm that isn't block expression"),
        "expected the missing-comma diagnostic, got {error:?}"
    );
}
