mod statement;
mod types;

use chumsky::input::ValueInput;
use chumsky::prelude::{empty, just, nested_delimiters, via_parser};
use chumsky::{extra, select, Parser};

use crate::error::{Diagnostic, Error, Span};
use crate::lexer::Token;
use crate::str::{AliasName, FunctionName, Identifier, ModuleName, SymbolName};

/// Trait for generating parsers of themselves.
///
/// Replacement for previous `PestParse` trait.
pub trait ChumskyParse: Sized {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>;
}

pub(super) type ParseError<'src> = extra::Err<Diagnostic>;

/// Identifiers of the built-in binary match patterns.
/// An enum may not use them as its name, because e.g. `Left::A` in a match arm would parse as the built-in `Left(..)` pattern.
pub(crate) const RESERVED_PATTERN_NAMES: [&str; 4] = ["Left", "Right", "Some", "None"];

macro_rules! impl_parse_wrapped_string {
    ($wrapper: ident, $label: literal) => {
        impl ChumskyParse for $wrapper {
            fn parser<'tokens, 'src: 'tokens, I>(
            ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
            where
                I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
            {
                select! {
                    Token::Ident(ident) => Self::from_str_unchecked(ident)
                }
                .labelled($label)
            }
        }
    };
}

impl_parse_wrapped_string!(SymbolName, "unresolved symbol name");
impl_parse_wrapped_string!(FunctionName, "function name");
impl_parse_wrapped_string!(Identifier, "identifier");
impl_parse_wrapped_string!(AliasName, "alias name");
impl_parse_wrapped_string!(ModuleName, "module name");

/// Parse a token, and, if not found, place itself in place of missing one.
///
/// Should be only used when we know that this token should be there. For example, type of
/// `List<ty, bound>` would require comma inside angle brackets.
pub(super) fn parse_token_with_recovery<'tokens, 'src: 'tokens, I>(
    tok: Token<'src>,
) -> impl Parser<'tokens, I, Token<'src>, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    just(tok.clone()).recover_with(via_parser(empty().to(tok)))
}

/// Parser with error recovery for expressions, which would always contains given delimiters.
///
/// Can track span of open delimiter (if any).
pub(super) fn delimited_with_recovery<'tokens, 'src: 'tokens, I, P, T, F>(
    parser: P,
    open: Token<'src>,
    close: Token<'src>,
    fallback: F,
) -> impl Parser<'tokens, I, T, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    P: Parser<'tokens, I, T, ParseError<'src>> + Clone,
    T: Clone + 'tokens,
    F: Fn(Span) -> T + Clone + 'tokens,
{
    just(open.clone())
        .map_with(|_, e| e.span())
        .then(parser.recover_with(via_parser(nested_delimiters(
            open.clone(),
            close.clone(),
            [
                (Token::LParen, Token::RParen),
                (Token::LBracket, Token::RBracket),
                (Token::LBrace, Token::RBrace),
                (Token::LAngle, Token::RAngle),
            ],
            fallback,
        ))))
        .then(just(close).or_not())
        // TODO: we should use information about open delimiter
        .validate(move |((open_span, content), close_token), _, emit| {
            if close_token.is_none() {
                emit.emit(
                    Error::Grammar {
                        msg: format!("Unclosed delimiter {open}"),
                    }
                    .with_span(open_span),
                )
            }
            content
        })
}
