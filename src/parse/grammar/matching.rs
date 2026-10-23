use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{choice, just};
use chumsky::{select, IterParser, Parser};
use either::Either;
use itertools::Itertools;

use crate::error::{Diagnostic, Error, Span};
use crate::lexer::Token;
use crate::pattern::Pattern;
use crate::str::{AliasName, Identifier};
use crate::types::AliasedType;

use super::super::{
    EnumMatch, EnumMatchArm, Expression, ExpressionInner, Match, MatchArm, MatchPattern,
    SingleExpressionInner,
};
use super::{delimited_with_recovery, ChumskyParse, ParseError, RESERVED_PATTERN_NAMES};

impl ChumskyParse for MatchPattern {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let wrapper = |name: &'static str, ctor: fn(Pattern, AliasedType) -> Self| {
            select! { Token::Ident(i) if i == name => i }
                .ignore_then(delimited_with_recovery(
                    Pattern::parser()
                        .then_ignore(just(Token::Colon))
                        .then(AliasedType::parser()),
                    Token::LParen,
                    Token::RParen,
                    |_| {
                        (
                            Pattern::Ignore,
                            AliasedType::alias(AliasName::from_str_unchecked("error")),
                        )
                    },
                ))
                .map(move |(id, ty)| ctor(id, ty))
        };

        choice((
            wrapper("Left", MatchPattern::Left),
            wrapper("Right", MatchPattern::Right),
            wrapper("Some", MatchPattern::Some),
            select! { Token::Ident("None") => MatchPattern::None },
            select! { Token::Bool(true) => MatchPattern::True },
            select! { Token::Bool(false) => MatchPattern::False },
        ))
    }
}

/// Head of an enum match arm, before the arm body is attached: `EnumName::Variant` with optional payload bindings.
#[derive(Clone)]
struct EnumArmHead {
    enum_path: Arc<[Identifier]>,
    variant: Identifier,
    bindings: Arc<[(Pattern, AliasedType)]>,
}

impl EnumArmHead {
    fn into_arm(self, expression: Arc<Expression>, span: Span) -> EnumMatchArm {
        EnumMatchArm {
            enum_path: self.enum_path,
            variant: self.variant,
            bindings: self.bindings,
            expression,
            span,
        }
    }
}

/// One parsed match arm. An enum variant head or a built-in pattern,
/// plus the arm body and its source boundaries.
type ParsedMatchArm = (Either<EnumArmHead, MatchPattern>, Arc<Expression>, Span);

/// Parser for the head of an enum match arm: `EnumName::Variant` with
/// optional payload bindings `(pattern: Type, ...)`.
///
/// A non-reserved head identifier commits without backtracking: the
/// `select!` guard fails without consuming the token. A reserved pattern
/// name (`Left`, `Some`, ...) heads an enum path only when `::` follows,
/// so an alias of an enum that shadows a pattern name stays matchable
/// while `Left(x)` remains the built-in pattern.
fn enum_arm_head_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, EnumArmHead, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    let bindings = Pattern::parser()
        .then_ignore(just(Token::Colon))
        .then(AliasedType::parser())
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .at_least(1)
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .or_not()
        .map(|bindings| Arc::from(bindings.unwrap_or_default()));

    let head_ident = choice((
        select! { Token::Ident(name) if !RESERVED_PATTERN_NAMES.contains(&name) => Identifier::from_str_unchecked(name) },
        // The rewind leaves the `::` for the shared `then_ignore` below.
        select! { Token::Ident(name) => Identifier::from_str_unchecked(name) }
            .then_ignore(just(Token::DoubleColon).rewind()),
    ));

    head_ident
        .then_ignore(just(Token::DoubleColon))
        .then(
            Identifier::parser()
                .separated_by(just(Token::DoubleColon))
                .at_least(1)
                .collect::<Vec<Identifier>>(),
        )
        .then(bindings)
        .map(|((first, mut rest), bindings)| {
            let variant = rest.pop().expect("the parser requires one segment");
            let mut enum_path = vec![first];
            enum_path.extend(rest);
            EnumArmHead {
                enum_path: Arc::from(enum_path),
                variant,
                bindings,
            }
        })
}

/// Parser for one match arm. An arm head, `=>`, the arm body, and the
/// comma that is required unless the body is a block expression.
fn match_arm_parser<'tokens, 'src: 'tokens, I, E>(
    expr: E,
) -> impl Parser<'tokens, I, ParsedMatchArm, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
{
    let arm_head = choice((
        enum_arm_head_parser().map(Either::Left),
        MatchPattern::parser().map(Either::Right),
    ));

    arm_head
        .then_ignore(just(Token::FatArrow))
        .then(expr.map(Arc::new))
        .then(just(Token::Comma).or_not())
        .validate(|((head, expression), comma), e, emitter| {
            let is_block = matches!(expression.as_ref().inner, ExpressionInner::Block(_, _));
            if !is_block && comma.is_none() {
                emitter.emit(
                    Error::Grammar {
                        msg: "Missing ',' after a match arm that isn't block expression"
                            .to_string(),
                    }
                    .with_span(e.span()),
                );
            }
            (head, expression, e.span())
        })
}

/// A binary match with dummy arms, standing in for a malformed match so
/// parsing can continue after its error was reported.
fn placeholder_match(scrutinee: Arc<Expression>, span: Span) -> SingleExpressionInner {
    let fallback_arm = MatchArm {
        expression: Arc::new(Expression::empty(Span::DUMMY)),
        pattern: MatchPattern::False,
        span: Span::DUMMY,
    };
    SingleExpressionInner::Match(Match {
        scrutinee,
        left: fallback_arm.clone(),
        right: fallback_arm,
        span,
    })
}

/// Do the two patterns complement each other in canonical order
/// (`Left`/`Right`, `None`/`Some`, `false`/`true`)?
fn patterns_in_canonical_order(left: &MatchPattern, right: &MatchPattern) -> bool {
    matches!(
        (left, right),
        (MatchPattern::Left(..), MatchPattern::Right(..))
            | (MatchPattern::None, MatchPattern::Some(..))
            | (MatchPattern::False, MatchPattern::True)
    )
}

/// Assemble parsed arms into an [`EnumMatch`] or a binary [`Match`] node.
///
/// Malformed arms return the error to report together with a fallback
/// node, so the caller emits exactly one error per malformed match.
/// Running bad arms through the pattern pairing would emit a second,
/// bogus "incompatible match arms" error for the same span.
fn assemble_match_arms(
    scrutinee: Arc<Expression>,
    arms: Vec<ParsedMatchArm>,
    span: Span,
) -> Result<SingleExpressionInner, Box<(Diagnostic, SingleExpressionInner)>> {
    if arms.is_empty() {
        return Err(Box::new((
            Error::Grammar {
                msg: "match expression has no arms".to_string(),
            }
            .with_span(span),
            placeholder_match(scrutinee, span),
        )));
    }

    // Split arms by the classification the arm heads carry. Any number of
    // enum arms (including one) routes to the enum match, whose analysis
    // reports missing variants. The binary arm-count error below would be misleading there.
    let (enum_arms, builtin_arms): (Vec<EnumMatchArm>, Vec<MatchArm>) = arms
        .into_iter()
        .partition_map(|(head, expression, arm_span)| match head {
            Either::Left(head) => Either::Left(head.into_arm(expression, arm_span)),
            Either::Right(pattern) => Either::Right(MatchArm {
                pattern,
                expression,
                span: arm_span,
            }),
        });

    if builtin_arms.is_empty() {
        return Ok(SingleExpressionInner::EnumMatch(EnumMatch {
            scrutinee,
            arms: Arc::from(enum_arms),
            span,
        }));
    }

    if let Some(enum_arm) = enum_arms.first() {
        // Mixed arms: name the clash instead of an arm-count error.
        return Err(Box::new((
            Error::Grammar {
                msg: format!(
                    "match arms mix the enum variant pattern `{}` \
                     with the built-in pattern `{}`",
                    enum_arm, builtin_arms[0].pattern
                ),
            }
            .with_span(span),
            placeholder_match(scrutinee, span),
        )));
    }

    // Binary match: exactly 2 built-in arms, in either order.
    let Ok([first, second]) = <[MatchArm; 2]>::try_from(builtin_arms) else {
        return Err(Box::new((
            Error::Grammar {
                msg: "binary match requires exactly 2 arms".to_string(),
            }
            .with_span(span),
            placeholder_match(scrutinee, span),
        )));
    };

    let (left, right) = if patterns_in_canonical_order(&first.pattern, &second.pattern) {
        (first, second)
    } else if patterns_in_canonical_order(&second.pattern, &first.pattern) {
        (second, first)
    } else {
        let error = Error::IncompatibleMatchArms {
            first: Box::new(first.pattern.clone()),
            second: Box::new(second.pattern.clone()),
        }
        .with_span(span);
        // The arms still form a match; keep them so analysis can continue.
        let node = SingleExpressionInner::Match(Match {
            scrutinee,
            left: first,
            right: second,
            span,
        });
        return Err(Box::new((error, node)));
    };

    Ok(SingleExpressionInner::Match(Match {
        scrutinee,
        left,
        right,
        span,
    }))
}

/// Parser for `match` expressions.
///
/// Handles both binary matches (exactly 2 arms: Left/Right, None/Some,
/// false/true) and enum matches (arms of the form `EnumName::Variant`).
/// Dispatches to [`Match`] or [`EnumMatch`] based on the patterns found.
pub(super) fn match_expr_parser<'tokens, 'src: 'tokens, I, E>(
    expr: E,
) -> impl Parser<'tokens, I, SingleExpressionInner, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
{
    let arms = delimited_with_recovery(
        match_arm_parser(expr.clone())
            .repeated()
            .collect::<Vec<_>>(),
        Token::LBrace,
        Token::RBrace,
        |_| vec![],
    );

    just(Token::Match)
        .ignore_then(expr.map(Arc::new))
        .then(arms)
        .validate(|(scrutinee, arms), e, emit| {
            match assemble_match_arms(scrutinee, arms, e.span()) {
                Ok(node) => node,
                Err(boxed) => {
                    let (error, fallback) = *boxed;
                    emit.emit(error);
                    fallback
                }
            }
        })
}
