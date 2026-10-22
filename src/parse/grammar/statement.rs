use chumsky::input::ValueInput;
use chumsky::prelude::{choice, just, recursive};
use chumsky::{select, IterParser, Parser};

use crate::error::Span;
use crate::lexer::Token;
use crate::pattern::Pattern;
use crate::str::Identifier;
use crate::types::AliasedType;

use super::super::{Assignment, Expression, Statement};
use super::{delimited_with_recovery, parse_token_with_recovery, ChumskyParse, ParseError};

impl Statement {
    pub(crate) fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let assignment = Assignment::parser(expr.clone()).map(Statement::Assignment);

        let expression = expr.map(Statement::Expression);

        choice((assignment, expression))
    }
}

impl Assignment {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        just(Token::Let)
            .ignore_then(Pattern::parser())
            .then_ignore(parse_token_with_recovery(Token::Colon))
            .then(AliasedType::parser())
            .then_ignore(parse_token_with_recovery(Token::Eq))
            .then(expr)
            .map_with(|((pattern, ty), expression), e| Self {
                pattern,
                ty,
                expression,
                span: e.span(),
            })
    }
}

impl ChumskyParse for Pattern {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|pat| {
            let variable = Identifier::parser().map(Pattern::Identifier);

            let ignore = select! {
                Token::Ident("_") => Pattern::Ignore,
            };

            let tuple = delimited_with_recovery(
                pat.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
                Token::LParen,
                Token::RParen,
                |_| Vec::new(),
            )
            .map(Pattern::tuple);

            let array = delimited_with_recovery(
                pat.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
                Token::LBracket,
                Token::RBracket,
                |_| Vec::new(),
            )
            .map(Pattern::array);

            choice((ignore, variable, tuple, array)).labelled("pattern")
        })
    }
}
