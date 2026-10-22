use crate::error::{DiagnosticManager, Span};
use crate::lexer::{FmtToken, FmtTokens};
use crate::unstable::UnstableFeatures;

use super::{pipeline, Program};

/// Source-aware parse result used by formatters.
///
/// The compiler keeps using [`Program`] directly. Formatters need the same
/// semantic tree plus the lossless trivia stream that the grammar intentionally
/// does not consume.
#[derive(Clone, Debug)]
pub struct ParsedSource<'src> {
    program: Program,
    tokens: FmtTokens<'src>,
    prefix: Span,
}

impl<'src> ParsedSource<'src> {
    /// Access the semantic program used for formatting.
    pub fn program(&self) -> &Program {
        &self.program
    }

    /// Access the lossless token stream in source order.
    pub fn tokens(&self) -> &FmtTokens<'src> {
        &self.tokens
    }

    /// Access the source prefix skipped by the version-directive prescan.
    ///
    /// A formatter should preserve this range verbatim until the directive gains
    /// its own formatting grammar.
    pub fn prefix(&self) -> Span {
        self.prefix
    }
}

impl Program {
    /// Parse source for formatting while retaining all comments and whitespace.
    pub fn parse_with_errors_for_fmt<'src>(
        file_id: usize,
        source: &'src str,
        unstable_features: &UnstableFeatures,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<ParsedSource<'src>> {
        let before = diagnostics.error_count();

        let start = pipeline::directive_prescan(source, file_id, diagnostics)?;

        let (tokens, lex_errors) = crate::lexer::lex_lossless(file_id, source, start);
        let lex_ok = pipeline::is_lex_ok(lex_errors, diagnostics)?;

        let tokens = tokens?;

        let semantic_tokens = tokens
            .iter()
            .filter_map(|(token, span)| match token {
                FmtToken::Token(token) => Some((token.clone(), *span)),
                FmtToken::Trivia(_) => None,
            })
            .collect::<Vec<_>>();

        let (program, parse_ok) =
            pipeline::parse_ast(file_id, source, semantic_tokens, diagnostics);

        if parse_ok && lex_ok {
            pipeline::post_check(unstable_features, program.as_ref(), diagnostics);
        }

        if diagnostics.error_count() > before {
            None
        } else {
            let program = program?;
            Some(ParsedSource {
                program,
                tokens,
                prefix: Span::new(file_id, 0..start),
            })
        }
    }
}
