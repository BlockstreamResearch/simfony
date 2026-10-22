use std::str::FromStr;
use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{choice, empty, just, none_of, recursive, via_parser};
use chumsky::{select, IterParser, Parser};

use crate::error::{Diagnostic, Error, Span};
use crate::lexer::Token;
use crate::num::NonZeroPow2Usize;
use crate::str::{AliasName, Decimal, Identifier};
use crate::types::{AliasedType, BuiltinAlias, TypeConstructible, UIntType};

use super::super::{EnumDeclaration, EnumVariant, TypeAlias, Visibility};
use super::{
    delimited_with_recovery, parse_token_with_recovery, ChumskyParse, ParseError,
    RESERVED_PATTERN_NAMES,
};

impl ChumskyParse for AliasedType {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let atom = select! {
                Token::Ident(ident) => {
                    if ident == "bool" {
                        AliasedType::boolean()
                    } else if let Ok(uint_type) = UIntType::from_str(ident) {
                        AliasedType::from(uint_type)
                    } else if let Ok(builtin) = BuiltinAlias::from_str(ident) {
                        AliasedType::builtin(builtin)
                    } else {
                        AliasedType::alias(AliasName::from_str_unchecked(ident))
                    }
                }
        };

        let num = select! {
            Token::DecLiteral(i) => i.clone()
        }
        .labelled("decimal number")
        .recover_with(via_parser(
            none_of([Token::RAngle, Token::RBracket])
                .ignored()
                .or(empty())
                .to(Decimal::from_str_unchecked("0")),
        ));

        recursive(|ty| {
            let args = delimited_with_recovery(
                ty.clone()
                    .then_ignore(parse_token_with_recovery(Token::Comma))
                    .then(ty.clone()),
                Token::LAngle,
                Token::RAngle,
                |_| {
                    (
                        AliasedType::alias(AliasName::from_str_unchecked("error")),
                        AliasedType::alias(AliasName::from_str_unchecked("error")),
                    )
                },
            );

            let sum_type = just(Token::Ident("Either"))
                .ignore_then(args)
                .map(|(left, right)| AliasedType::either(left, right))
                .labelled("Either");

            let option_type = just(Token::Ident("Option"))
                .ignore_then(delimited_with_recovery(
                    ty.clone(),
                    Token::LAngle,
                    Token::RAngle,
                    |_| AliasedType::alias(AliasName::from_str_unchecked("error")),
                ))
                .map(AliasedType::option)
                .labelled("Option");

            let tuple = delimited_with_recovery(
                ty.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect()
                    .map(|s: Vec<AliasedType>| AliasedType::tuple(s)),
                Token::LParen,
                Token::RParen,
                |_| AliasedType::tuple(Vec::new()),
            )
            .labelled("tuple");

            let array = delimited_with_recovery(
                ty.clone()
                    .then_ignore(parse_token_with_recovery(Token::Semi))
                    .then(num.clone())
                    .map(|(ty, size)| {
                        let digits =
                            crate::str::underscore_parsing::strip_digit_separators(size.as_inner());

                        AliasedType::array(ty, usize::from_str(digits.as_ref()).unwrap_or_default())
                    }),
                Token::LBracket,
                Token::RBracket,
                |_| {
                    AliasedType::array(
                        AliasedType::alias(AliasName::from_str_unchecked("error")),
                        0,
                    )
                },
            )
            .labelled("array");

            let list = just(Token::Ident("List"))
                .ignore_then(delimited_with_recovery(
                    ty.then_ignore(parse_token_with_recovery(Token::Comma))
                        .then(num.clone().validate(|num, e, emit| -> NonZeroPow2Usize {
                            let digits = crate::str::underscore_parsing::strip_digit_separators(
                                num.as_inner(),
                            );

                            match NonZeroPow2Usize::from_str(digits.as_ref()) {
                                Ok(number) => number,
                                Err(err) => {
                                    emit.emit(
                                        Error::Grammar {
                                            msg: format!("Cannot parse list bound: {err}"),
                                        }
                                        .with_span(e.span()),
                                    );
                                    // fallback to default value
                                    NonZeroPow2Usize::TWO
                                }
                            }
                        })),
                    Token::LAngle,
                    Token::RAngle,
                    |_| {
                        (
                            AliasedType::alias(AliasName::from_str_unchecked("error")),
                            NonZeroPow2Usize::TWO,
                        )
                    },
                ))
                .map(|(ty, size)| AliasedType::list(ty, size))
                .labelled("List");

            choice((sum_type, option_type, tuple, array, list, atom))
                .map_with(|inner, _| inner)
                .labelled("type")
        })
    }
}

impl ChumskyParse for TypeAlias {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        let name = AliasName::parser()
            .validate(|name, e, emit| {
                let ident = name.as_str();
                let known_type = if ident == "bool" {
                    Some(AliasedType::boolean())
                } else if let Ok(uint_type) = UIntType::from_str(ident) {
                    Some(AliasedType::from(uint_type))
                } else if let Ok(builtin) = BuiltinAlias::from_str(ident) {
                    Some(AliasedType::builtin(builtin))
                } else {
                    None
                };

                if known_type.is_some() {
                    emit.emit(
                        Error::RedefinedAliasAsBuiltin { name: name.clone() }.with_span(e.span()),
                    );
                }
                name
            })
            .map_with(|name, e| (name, e.span()));

        visibility
            .then(
                just(Token::Type)
                    .ignore_then(name)
                    .then_ignore(parse_token_with_recovery(Token::Eq))
                    .then(AliasedType::parser())
                    .then_ignore(just(Token::Semi)),
            )
            .map_with(|(visibility, (name, ty)), e| Self {
                visibility,
                name: name.0,
                ty,
                span: e.span(),
            })
    }
}

impl ChumskyParse for EnumDeclaration {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        let name = AliasName::parser().try_map(|name, span| {
            if RESERVED_PATTERN_NAMES.contains(&name.as_str()) {
                return Err(Diagnostic::new(
                    Error::Grammar {
                        msg: format!(
                            "enum name '{name}' is reserved for the built-in match pattern `{name}`"
                        ),
                    },
                    span,
                ));
            }
            // Reserved type names are rejected via the shared list, which
            // also covers the generic constructors (`Either`, `Option`,
            // `List`): `enum Signature` or `enum Option` would make
            // constructions name the enum while type annotations resolve
            // to the builtin, and the ABI would report the bare name
            // ambiguously.
            if crate::str::is_reserved_alias_name(name.as_str()) {
                return Err(Diagnostic::new(
                    Error::RedefinedAliasAsBuiltin { name: name.clone() },
                    span,
                ));
            }
            Ok(name)
        });

        let payload = AliasedType::parser()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .or_not()
            .map(|payload| Arc::from(payload.unwrap_or_default()));

        let variant = Identifier::parser()
            .then(payload)
            .map_with(|(name, payload), e| EnumVariant {
                name,
                payload,
                span: e.span(),
            });

        let variants = variant
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(Arc::from);

        visibility
            .then_ignore(just(Token::Enum))
            .then(name)
            .then(variants)
            .map_with(|((visibility, name), variants), e| Self {
                visibility,
                name,
                variants,
                span: e.span(),
            })
    }
}
