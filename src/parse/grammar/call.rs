use std::num::NonZeroUsize;
use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{choice, just};
use chumsky::{select, IterParser, Parser};

use crate::error::{Error, Span};
use crate::lexer::Token;
use crate::num::NonZeroPow2Usize;
use crate::str::{FunctionName, JetName};
use crate::types::AliasedType;

use super::super::{Call, CallName, Expression};
use super::{delimited_with_recovery, parse_token_with_recovery, ChumskyParse, ParseError};

impl Call {
    pub(super) fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let args = delimited_with_recovery(
            expr.separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<_>>(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(Arc::from)
        .labelled("call arguments");

        CallName::parser()
            .then(args)
            .map_with(|(name, args), e| Self {
                name,
                args,
                span: e.span(),
            })
    }
}

impl ChumskyParse for CallName {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let turbofish_start = just(Token::DoubleColon).then(just(Token::LAngle)).ignored();

        let generics_close = just(Token::RAngle);

        let type_cast = just(Token::LAngle)
            .ignore_then(AliasedType::parser())
            .then_ignore(generics_close.clone())
            .then_ignore(just(Token::DoubleColon))
            .then_ignore(just(Token::Ident("into")))
            .map(CallName::TypeCast);

        let builtin_generic_ty = |name: &'static str, ctor: fn(AliasedType) -> Self| {
            just(Token::Ident(name))
                .ignore_then(turbofish_start.clone())
                .ignore_then(AliasedType::parser())
                .then_ignore(generics_close.clone())
                .map(ctor)
        };

        let unwrap_left = builtin_generic_ty("unwrap_left", CallName::UnwrapLeft);
        let unwrap_right = builtin_generic_ty("unwrap_right", CallName::UnwrapRight);
        let is_none = builtin_generic_ty("is_none", CallName::IsNone);
        let raw_hash = builtin_generic_ty("raw_hash", CallName::RawHash);

        let fold = just(Token::Ident("fold"))
            .ignore_then(turbofish_start.clone())
            .ignore_then(FunctionName::parser())
            .then_ignore(parse_token_with_recovery(Token::Comma))
            .then(select! { Token::DecLiteral(s) => s }.labelled("list size"))
            .then_ignore(generics_close.clone())
            .validate(|(func, bound_str), e, emit| {
                let digits =
                    crate::str::underscore_parsing::strip_digit_separators(bound_str.as_inner());

                let bound = match digits.parse::<usize>() {
                    Ok(num) => match NonZeroPow2Usize::new(num) {
                        Some(val) => val,
                        None => {
                            emit.emit(Error::ListBoundPow2 { bound: num }.with_span(e.span()));
                            NonZeroPow2Usize::TWO
                        }
                    },
                    Err(_) => {
                        emit.emit(
                            Error::CannotParse {
                                msg: format!("Invalid number: {}", bound_str),
                            }
                            .with_span(e.span()),
                        );
                        NonZeroPow2Usize::TWO
                    }
                };

                CallName::Fold(func, bound)
            });

        let array_fold = just(Token::Ident("array_fold"))
            .ignore_then(turbofish_start.clone())
            .ignore_then(FunctionName::parser())
            .then_ignore(parse_token_with_recovery(Token::Comma))
            .then(select! { Token::DecLiteral(s) => s }.labelled("array size"))
            .then_ignore(generics_close.clone())
            .validate(|(func, size_str), e, emit| {
                let digits =
                    crate::str::underscore_parsing::strip_digit_separators(size_str.as_inner());

                let size = match digits.parse::<usize>() {
                    Ok(0) => {
                        emit.emit(Error::ArraySizeNonZero { size: 0 }.with_span(e.span()));
                        NonZeroUsize::new(1).unwrap()
                    }
                    Ok(n) => NonZeroUsize::new(n).unwrap(),
                    Err(_) => {
                        emit.emit(
                            Error::CannotParse {
                                msg: format!("Invalid number: {}", size_str),
                            }
                            .with_span(e.span()),
                        );
                        NonZeroUsize::new(1).unwrap()
                    }
                };

                CallName::ArrayFold(func, size)
            });

        let for_while = just(Token::Ident("for_while"))
            .ignore_then(turbofish_start.clone())
            .ignore_then(FunctionName::parser())
            .then_ignore(generics_close.clone())
            .map(CallName::ForWhile);

        let simple_builtins = select! {
            Token::Ident("unwrap") => CallName::Unwrap,
            Token::Macro("assert!") => CallName::Assert,
            Token::Macro("panic!") => CallName::Panic,
            Token::Macro("dbg!") => CallName::Debug,
        };

        let jet = select! { Token::Jet(s) => JetName::from_str_unchecked(s) }.map(CallName::Jet);

        let custom_func = FunctionName::parser().map(CallName::Custom);

        choice((
            type_cast,
            unwrap_left,
            unwrap_right,
            is_none,
            fold,
            array_fold,
            for_while,
            raw_hash,
            simple_builtins,
            jet,
            custom_func,
        ))
    }
}
