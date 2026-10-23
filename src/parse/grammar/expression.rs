use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{
    any, choice, just, nested_delimiters, one_of, recursive, skip_then_retry_until,
};
use chumsky::{select, IterParser, Parser};
use either::Either;

use crate::error::{Diagnostic, Error, Span};
use crate::lexer::Token;
use crate::str::Identifier;
use crate::TemplateProgramWitness;

use super::super::{
    Call, EnumConstruction, Expression, ExpressionInner, SingleExpression, SingleExpressionInner,
    Statement,
};
use super::matching::match_expr_parser;
use super::{delimited_with_recovery, ChumskyParse, ParseError};

/// Split a parsed block body into its statements and its optional final expression.
///
/// Each element arrives paired with the `;` that followed it, if any. Only the last
/// element may omit its `;`, and only when it is an expression rather than an
/// assignment: that element is the block's final expression. Every other missing `;`
/// is reported, and the element is kept as a statement so that analysis of the rest
/// of the block still happens.
fn split_block_body(
    elements: Vec<(Statement, Option<Token<'_>>)>,
    emit: &mut chumsky::input::Emitter<Diagnostic>,
) -> (Arc<[Statement]>, Option<Arc<Expression>>) {
    let count = elements.len();
    let mut statements = Vec::with_capacity(count);
    let mut final_expr = None;

    for (index, (statement, semi)) in elements.into_iter().enumerate() {
        if semi.is_some() {
            statements.push(statement);
            continue;
        }

        match statement {
            // A trailing expression without `;` is the block's value.
            Statement::Expression(expression) if index + 1 == count => {
                final_expr = Some(Arc::new(expression));
            }
            statement => {
                emit.emit(
                    Error::Grammar {
                        msg: "Expected `;` after statement".to_string(),
                    }
                    .with_span(*statement.span()),
                );
                statements.push(statement);
            }
        }
    }

    (Arc::from(statements), final_expr)
}

impl ChumskyParse for Expression {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|expr| {
            let block = {
                // A block body is a run of elements, each of which is a statement
                // followed by `;`, except that the last one may drop the `;` and
                // become the block's final expression.
                let element = Statement::parser(expr.clone()).then(just(Token::Semi).or_not());

                let block_recovery = nested_delimiters(
                    Token::LBrace,
                    Token::RBrace,
                    [
                        (Token::LParen, Token::RParen),
                        (Token::LAngle, Token::RAngle),
                        (Token::LBracket, Token::RBracket),
                    ],
                    |span| Expression::empty(span).inner().clone(),
                );

                let body = element
                    .repeated()
                    .collect::<Vec<_>>()
                    .validate(|elements, _, emit| split_block_body(elements, emit))
                    .recover_with(skip_then_retry_until(
                        block_recovery.ignored().or(any().ignored()),
                        one_of([Token::Semi, Token::RParen, Token::RBracket, Token::RBrace])
                            .ignored(),
                    ));

                delimited_with_recovery(body, Token::LBrace, Token::RBrace, |_| {
                    (Arc::from(Vec::new()), None)
                })
                .map(|(stmts, end_expr)| ExpressionInner::Block(stmts, end_expr))
            };

            let single = SingleExpression::parser(expr.clone()).map(ExpressionInner::Single);

            choice((block, single))
                .map_with(|inner, e| Expression {
                    inner,
                    span: e.span(),
                })
                .labelled("expression")
        })
    }
}

impl SingleExpression {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let wrapper = |name: &'static str| {
            select! { Token::Ident(i) if i == name => i }.ignore_then(
                expr.clone()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
        };

        let left =
            wrapper("Left").map(|e| SingleExpressionInner::Either(Either::Left(Arc::new(e))));

        let right =
            wrapper("Right").map(|e| SingleExpressionInner::Either(Either::Right(Arc::new(e))));

        let some = wrapper("Some").map(|e| SingleExpressionInner::Option(Some(Arc::new(e))));

        // Bare `None` is the option literal only when no `::` follows:
        // `None::A` is a construction of an enum aliased as `None`, and
        // must fall through to the enum-construction alternative.
        let none = select! { Token::Ident("None") => SingleExpressionInner::Option(None) }
            .then_ignore(just(Token::DoubleColon).not().rewind());

        let boolean = select! { Token::Bool(b) => SingleExpressionInner::Boolean(b) };

        let comma_separated = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>();

        let array = delimited_with_recovery(
            comma_separated.clone(),
            Token::LBracket,
            Token::RBracket,
            |_| Vec::new(),
        )
        .map(|es| SingleExpressionInner::Array(Arc::from(es)));

        let list = just(Token::Macro("list!"))
            .ignore_then(delimited_with_recovery(
                comma_separated.clone(),
                Token::LBracket,
                Token::RBracket,
                |_| Vec::new(),
            ))
            .map(|es| SingleExpressionInner::List(Arc::from(es)));

        let tuple = delimited_with_recovery(
            comma_separated.clone(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(|es| SingleExpressionInner::Tuple(Arc::from(es)));

        let literal = select! {
            Token::DecLiteral(s) => SingleExpressionInner::Decimal(s),
            Token::HexLiteral(s) => SingleExpressionInner::Hexadecimal(s),
            Token::BinLiteral(s) => SingleExpressionInner::Binary(s),
            Token::Witness(s) => SingleExpressionInner::Witness(TemplateProgramWitness::witness_from_str(s)),
            Token::Param(s) => SingleExpressionInner::Parameter(TemplateProgramWitness::parameter_from_str(s)),
        };

        // Enum variant construction: `Path::To::Enum::Variant(args..)`.
        // At least one `::` distinguishes the path from variables and calls.
        // The built-in wrappers (Left, Some, ...) require `(` directly after
        // their name, so they never reach this alternative.
        let enum_construction = Identifier::parser()
            .separated_by(just(Token::DoubleColon))
            .at_least(2)
            .collect::<Vec<Identifier>>()
            .then(
                comma_separated
                    .clone()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not(),
            )
            .map_with(|(mut segments, args), e| {
                let variant = segments.pop().expect("the parser requires two segments");
                EnumConstruction {
                    enum_path: Arc::from(segments),
                    variant,
                    args: Arc::from(args.unwrap_or_default()),
                    span: e.span(),
                }
            })
            .map(SingleExpressionInner::EnumConstruction);

        let call = Call::parser(expr.clone()).map(SingleExpressionInner::Call);

        let match_expr = match_expr_parser(expr.clone());

        let variable = Identifier::parser().map(SingleExpressionInner::Variable);

        // Expression delimeted by parentheses
        let expression = expr
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|es| SingleExpressionInner::Expression(Arc::from(es)));

        choice((
            left,
            right,
            some,
            none,
            boolean,
            match_expr,
            expression,
            list,
            array,
            tuple,
            enum_construction,
            call,
            literal,
            variable,
        ))
        .map_with(|inner, e| Self {
            inner,
            span: e.span(),
        })
    }
}
