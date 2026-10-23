use chumsky::input::Input;
use chumsky::Parser;

use crate::driver::MAIN_MODULE;
use crate::error::{Diagnostic, DiagnosticManager, Error, Span};
use crate::lexer::Tokens;
use crate::unstable::{RequireFeature, UnstableFeatures};
use crate::version::SimcDirective;

use super::grammar::ChumskyParse;

/// Copy of [`FromStr`] that internally uses the `chumsky` parser.
///
/// [`FromStr`]: std::str::FromStr
pub trait ParseFromStr: Sized {
    /// Parse a value from the string `s`.
    fn parse_from_str(s: &str) -> Result<Self, Diagnostic>;
}

/// Trait for parsing with collection of errors.
pub trait ParseFromStrWithErrors: Sized {
    /// Parse a value from the string `content` with Errors.
    ///
    /// Feature-gated syntax in the parsed AST is checked against
    /// `unstable_features`; uses of disabled features are pushed to `diagnostics`.
    fn parse_from_str_with_errors(
        file_id: usize,
        content: &str,
        unstable_features: &UnstableFeatures,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Self>;
}

trait AstNode: ChumskyParse + crate::unstable::RequireFeature + std::fmt::Debug {}

impl<T> AstNode for T where T: ChumskyParse + crate::unstable::RequireFeature + std::fmt::Debug {}

/// This implementation only returns first encountered error.
impl<A: ChumskyParse + std::fmt::Debug> ParseFromStr for A {
    fn parse_from_str(s: &str) -> Result<Self, Diagnostic> {
        let (tokens, mut lex_errs) = crate::lexer::lex(MAIN_MODULE, s, 0);

        // The `simc` directive is source-file syntax, so fragments have no prescan
        // and `simc` lexes as a reserved keyword. Its `"<range>";` remnant does not
        // lex either, so the first reserved-keyword error is reported alone.
        if let Some(err) = lex_errs
            .iter()
            .find(|diag| matches!(diag.error(), Error::ReservedSimcKeyword))
        {
            return Err(err.clone());
        }

        let Some(tokens) = tokens else {
            return Err(lex_errs
                .pop()
                .unwrap_or(Diagnostic::global(Error::CannotParse {
                    msg: "Empty token stream without an error".to_string(),
                })));
        };

        let (ast, parse_errs) = A::parser()
            .map_with(|parsed, _| parsed)
            .parse(
                tokens
                    .as_slice()
                    .map(Span::eof(MAIN_MODULE, s.len()), |(t, s)| (t, s)),
            )
            .into_output_errors();

        if parse_errs.is_empty() {
            Ok(ast.ok_or(Diagnostic::global(Error::CannotParse {
                msg: "Empty AST without an error.".to_string(),
            }))?)
        } else {
            let err = parse_errs.first().unwrap().clone();
            Err(err)
        }
    }
}

impl<A: AstNode> ParseFromStrWithErrors for A {
    fn parse_from_str_with_errors(
        file_id: usize,
        content: &str,
        unstable_features: &UnstableFeatures,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Self> {
        let before = diagnostics.error_count();

        let start = directive_prescan(content, file_id, diagnostics)?;

        let (tokens, lex_errs) = crate::lexer::lex(file_id, content, start);

        let lex_ok = is_lex_ok(lex_errs, diagnostics)?;

        let tokens = tokens?;

        let (ast, parse_status) = parse_ast::<A>(file_id, content, tokens, diagnostics);

        if lex_ok && parse_status {
            let () = post_check(unstable_features, ast.as_ref(), diagnostics);
        }

        // TODO: We should return parsed result if we found errors, but because analyzing in `ast` module
        // is not handling poisoned tree right now, we don't return parsed result
        if diagnostics.error_count() > before {
            None
        } else {
            ast
        }
    }
}

/// Handle the `simc` directive before lexing: an incompatible or malformed
/// directive is reported as the only diagnostic (the rest is noise), and
/// lexing starts right after a valid one, so the lexer and grammar never
/// see it.
pub(super) fn directive_prescan(
    content: &str,
    file_id: usize,
    diagnostics: &mut DiagnosticManager,
) -> Option<usize> {
    match SimcDirective::prescan(content, file_id) {
        Ok(start) => Some(start),
        Err(box_error) => {
            let (err, span) = *box_error;
            diagnostics.push(Diagnostic::new(err, span));
            None
        }
    }
}

pub(super) fn is_lex_ok(
    mut lex_errs: Vec<Diagnostic>,
    diagnostics: &mut DiagnosticManager,
) -> Option<bool> {
    // A stray `simc` makes every other diagnostic noise — its `"<range>";` remnant
    // does not lex — so the reserved-keyword errors are reported alone.
    if lex_errs
        .iter()
        .any(|e| matches!(e.error(), Error::ReservedSimcKeyword))
    {
        lex_errs.retain(|e| matches!(e.error(), Error::ReservedSimcKeyword));
        diagnostics.extend(lex_errs);
        None
    } else {
        let lex_ok = lex_errs.is_empty();
        diagnostics.extend(lex_errs);
        Some(lex_ok)
    }
}

pub(super) fn parse_ast<T: ChumskyParse>(
    file_id: usize,
    src: &str,
    tokens: Tokens<'_>,
    diagnostics: &mut DiagnosticManager,
) -> (Option<T>, bool) {
    let eoi = Span::eof(file_id, src.len());
    let (ast, parse_errs) = T::parser()
        .parse(tokens.as_slice().map(eoi, |(t, s)| (t, s)))
        .into_output_errors();

    let parse_ok = parse_errs.is_empty();
    diagnostics.extend(parse_errs);
    (ast, parse_ok)
}

pub(super) fn post_check<T: RequireFeature>(
    unstable_features: &UnstableFeatures,
    program: Option<&T>,
    diagnostics: &mut DiagnosticManager,
) {
    if let Some(ast) = program {
        unstable_features.check_program(ast, diagnostics);
    }
}
