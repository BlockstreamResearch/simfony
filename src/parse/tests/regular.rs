use crate::driver::MAIN_MODULE;
use crate::error::{DiagnosticManager, Span};
use crate::parse::grammar::RESERVED_PATTERN_NAMES;
use crate::parse::{
    self, ExpressionInner, Item, ParseFromStr, ParseFromStrWithErrors, Program, UseDecl, UseItems,
    Visibility,
};
use crate::str::Identifier;
use crate::UnstableFeatures;

impl UseDecl {
    /// Creates a dummy `UseDecl` specifically for testing `DependencyMap` resolution.
    pub fn dummy_path(path: Vec<Identifier>) -> Self {
        Self {
            visibility: Visibility::default(),
            path,
            items: UseItems::List(Vec::new()),
            span: Span::DUMMY,
        }
    }
}

#[test]
fn test_double_colon() {
    let input = "fn main() { let ab: u8 = <(u4, u4)> : :into((0b1011, 0b1101)); }";
    let mut diagnostics = DiagnosticManager::new();

    let parsed_program = Program::parse_from_str_with_errors(
        MAIN_MODULE,
        input,
        &UnstableFeatures::all(),
        &mut diagnostics,
    );

    assert!(parsed_program.is_none());
    assert!(diagnostics.to_string().contains("Expected '::', found ':'"));
}

#[test]
fn test_double_double_colon() {
    let input = "fn main() { let pk: Pubkey = witnes::::PK; }";
    let mut diagnostics = DiagnosticManager::new();

    let parsed_program = Program::parse_from_str_with_errors(
        MAIN_MODULE,
        input,
        &UnstableFeatures::all(),
        &mut diagnostics,
    );

    assert!(parsed_program.is_none());
    assert!(
        diagnostics
            .to_string()
            .contains("Expected identifier, found ::"),
        "the second :: should be reported as the error site"
    );
}

/// Parse `input` and return whether it was rejected and the collected error text.
fn parse_with(input: &str, features: &UnstableFeatures) -> (bool, String) {
    let mut diagnostics = DiagnosticManager::new();
    let program =
        Program::parse_from_str_with_errors(MAIN_MODULE, input, features, &mut diagnostics);

    let rejected = program.is_none();
    let text = diagnostics.to_string();

    (rejected, text)
}

/// Nested blocks must parse in time linear in their depth.
#[test]
fn nested_blocks_parse_without_exponential_backtracking() {
    let depth = 32;
    let input = format!(
        "fn main() {{\n    let x: u32 = {}0{};\n    assert!(jet::eq_32(x, 0));\n}}",
        "{".repeat(depth),
        "}".repeat(depth)
    );

    let (rejected, text) = parse_with(&input, &UnstableFeatures::all());
    assert!(!rejected, "nested blocks must parse: {text}");
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
    let mut diagnostics = DiagnosticManager::new();
    let program = Program::parse_from_str_with_errors(
        MAIN_MODULE,
        src,
        &UnstableFeatures::all(),
        &mut diagnostics,
    );

    assert!(program.is_none(), "garbage input must be rejected");
    assert!(diagnostics.has_errors());
}

#[test]
fn recovery_synchronizes_at_enum_declaration() {
    // Discriminating setup: an invalid prefix followed by a malformed
    // enum. Without `Token::Enum` in the synchronization set the whole
    // enum is swallowed into the prefix's recovery span and only one
    // error is reported; with it, the enum parses as its own item and
    // its malformation is reported as a second error.
    let mut diagnostics = DiagnosticManager::new();
    let program = Program::parse_from_str_with_errors(
        MAIN_MODULE,
        "let invalid = 1;\nenum Action { A B }\nfn main() {}",
        &UnstableFeatures::all(),
        &mut diagnostics,
    );

    assert!(program.is_none(), "the invalid program must be rejected");
    assert_eq!(
        2,
        diagnostics.error_count(),
        "the invalid prefix and the malformed enum must each report an error"
    );
}

#[test]
fn recovery_after_malformed_enum_reaches_next_item() {
    let (rejected, _text) = parse_with(
        "enum Action { A B }\nfn main() {}",
        &UnstableFeatures::all(),
    );

    assert!(rejected, "a malformed enum must fail compilation");
}

#[test]
fn malformed_construct_containing_enum_keyword_reports_errors() {
    // `enum` inside a badly malformed nested construct may be mistaken
    // for an item boundary; compilation must still fail cleanly.
    let (rejected, _text) = parse_with(
        "fn broken() { let x = (enum; }\nfn main() {}",
        &UnstableFeatures::all(),
    );

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
        let program = parse::Program::parse_from_str(input).expect("parsing works");
        assert_eq!(program.to_string(), format!("{input}\n"));
    }
}

#[test]
fn statement_spans_exclude_terminating_semicolons() {
    let input = "fn main() { let value: u8 = 0; value; }";
    let program = Program::parse_from_str(input).expect("program parses");

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
    let program = parse::Program::parse_from_str(input).expect("parsing should succeed");
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
        let result = Program::parse_from_str(&format!("enum {reserved} {{ A, B, }}"));
        let error = result.expect_err(&format!("enum name {reserved} is reserved"));

        assert!(
            error.to_string().contains("reserved"),
            "error should say the name is reserved: {error}"
        );
    }
}
