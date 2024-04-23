//! Compile the parsed ast into a simplicity program

use std::str::FromStr;

use simplicity::{jet::Elements, Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::error::{Error, RichError, WithSpan};
use crate::num::NonZeroPow2Usize;
use crate::parse::{Pattern, SingleExpressionInner, Span, UIntType};
use crate::{
    named::{ConstructExt, ProgExt},
    parse::{Expression, ExpressionInner, FuncCall, FuncType, Program, Statement, Type},
    scope::GlobalScope,
    ProgNode,
};

fn eval_blk(
    stmts: &[Statement],
    scope: &mut GlobalScope,
    index: usize,
    last_expr: Option<&Expression>,
) -> Result<ProgNode, RichError> {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.eval(scope, None),
            None => Ok(ProgNode::unit()),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression.eval(scope, assignment.ty.as_ref())?;
            scope.insert(assignment.pattern.clone());
            let left = ProgNode::pair(expr, ProgNode::iden()).with_span(assignment.span)?;
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            ProgNode::comp(left, right).with_span(assignment.span)
        }
        Statement::FuncCall(func_call) => {
            let left = func_call.eval(scope, None)?;
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            let pair = ProgNode::pair(left, right).with_span(func_call.span)?;
            let drop_iden = ProgNode::drop_(ProgNode::iden());
            ProgNode::comp(pair, drop_iden).with_span(func_call.span)
        }
    }
}

impl Program {
    pub fn eval(&self, scope: &mut GlobalScope) -> Result<ProgNode, RichError> {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl FuncCall {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        _reqd_ty: Option<&Type>,
    ) -> Result<ProgNode, RichError> {
        let args = match self.args.is_empty() {
            true => SingleExpressionInner::Unit,
            false => SingleExpressionInner::Array(self.args.clone()),
        };
        let args_expr = args.eval(scope, None, self.span)?;

        match &self.func_type {
            FuncType::Jet(name) => {
                let jet = Elements::from_str(name)
                    .map_err(|_| Error::JetDoesNotExist(name.clone()))
                    .with_span(self.span)?;
                let jet_expr = ProgNode::jet(jet);
                ProgNode::comp(args_expr, jet_expr).with_span(self.span)
            }
            FuncType::BuiltIn(..) => unimplemented!("Builtins are not supported yet"),
            FuncType::UnwrapLeft => {
                debug_assert!(self.args.len() == 1);
                let left_and_unit =
                    ProgNode::pair(args_expr, ProgNode::unit()).with_span(self.span)?;
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertl(take_iden, fail_cmr).with_span(self.span)?;
                ProgNode::comp(left_and_unit, get_inner).with_span(self.span)
            }
            FuncType::UnwrapRight | FuncType::Unwrap => {
                debug_assert!(self.args.len() == 1);
                let right_and_unit =
                    ProgNode::pair(args_expr, ProgNode::unit()).with_span(self.span)?;
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertr(fail_cmr, take_iden).with_span(self.span)?;
                ProgNode::comp(right_and_unit, get_inner).with_span(self.span)
            }
        }
    }
}

impl Expression {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&Type>,
    ) -> Result<ProgNode, RichError> {
        match &self.inner {
            ExpressionInner::BlockExpression(stmts, expr) => {
                scope.push_scope();
                let res = eval_blk(stmts, scope, 0, Some(expr.as_ref()));
                scope.pop_scope();
                res
            }
            ExpressionInner::SingleExpression(e) => e.inner.eval(scope, reqd_ty, self.span),
        }
    }
}

impl SingleExpressionInner {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&Type>,
        span: Span,
    ) -> Result<ProgNode, RichError> {
        let expr = match self {
            SingleExpressionInner::Unit => ProgNode::unit(),
            SingleExpressionInner::Left(l) => {
                let l = l.eval(scope, None)?;
                ProgNode::injl(l)
            }
            SingleExpressionInner::None => ProgNode::injl(ProgNode::unit()),
            SingleExpressionInner::Right(r) | SingleExpressionInner::Some(r) => {
                let r = r.eval(scope, None)?;
                ProgNode::injr(r)
            }
            SingleExpressionInner::False => ProgNode::injl(ProgNode::unit()),
            SingleExpressionInner::True => ProgNode::injr(ProgNode::unit()),
            SingleExpressionInner::Product(l, r) => {
                let l = l.eval(scope, None)?;
                let r = r.eval(scope, None)?;
                ProgNode::pair(l, r).with_span(span)?
            }
            SingleExpressionInner::UnsignedInteger(decimal) => {
                let reqd_ty = reqd_ty.cloned().unwrap_or(Type::UInt(UIntType::U32));
                let ty = reqd_ty
                    .to_uint()
                    .ok_or(Error::TypeValueMismatch(reqd_ty))
                    .with_span(span)?;
                let value = ty.parse_decimal(decimal).with_span(span)?;
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value)).with_span(span)?
            }
            SingleExpressionInner::BitString(bits) => {
                let value = bits.to_simplicity();
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value)).with_span(span)?
            }
            SingleExpressionInner::ByteString(bytes) => {
                let value = bytes.to_simplicity();
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value)).with_span(span)?
            }
            SingleExpressionInner::Witness(name) => {
                scope.insert_witness(name.clone());
                ProgNode::witness(name.as_inner().clone())
            }
            SingleExpressionInner::Variable(identifier) => scope
                .get(identifier)
                .ok_or(Error::UndefinedVariable(identifier.clone()))
                .with_span(span)?,
            SingleExpressionInner::FuncCall(call) => call.eval(scope, reqd_ty)?,
            SingleExpressionInner::Expression(expression) => expression.eval(scope, reqd_ty)?,
            SingleExpressionInner::Match {
                scrutinee,
                left,
                right,
            } => {
                let mut l_scope = scope.clone();
                l_scope.insert(
                    left.pattern
                        .get_identifier()
                        .cloned()
                        .map(Pattern::Identifier)
                        .unwrap_or(Pattern::Ignore),
                );
                let l_compiled = left.expression.eval(&mut l_scope, reqd_ty)?;

                let mut r_scope = scope.clone();
                r_scope.insert(
                    right
                        .pattern
                        .get_identifier()
                        .cloned()
                        .map(Pattern::Identifier)
                        .unwrap_or(Pattern::Ignore),
                );
                let r_compiled = right.expression.eval(&mut r_scope, reqd_ty)?;

                // TODO: Enforce target type A + B for m_expr
                let scrutinized_input = scrutinee.eval(scope, None)?;
                let input = ProgNode::pair(scrutinized_input, ProgNode::iden()).with_span(span)?;
                let output = ProgNode::case(l_compiled, r_compiled).with_span(span)?;
                ProgNode::comp(input, output).with_span(span)?
            }
            SingleExpressionInner::Array(elements) => {
                let el_type = if let Some(Type::Array(ty, _)) = reqd_ty {
                    Some(ty.as_ref())
                } else {
                    None
                };
                let nodes = elements
                    .iter()
                    .map(|e| e.eval(scope, el_type))
                    .collect::<Result<Vec<_>, _>>()?;
                let tree = BTreeSlice::from_slice(&nodes);
                tree.fold(ProgNode::pair_unwrap)
            }
            SingleExpressionInner::List(elements) => {
                let el_type = if let Some(Type::List(ty, _)) = reqd_ty {
                    Some(ty.as_ref())
                } else {
                    None
                };
                let nodes = elements
                    .iter()
                    .map(|e| e.eval(scope, el_type))
                    .collect::<Result<Vec<_>, _>>()?;
                let bound = if let Some(Type::List(_, bound)) = reqd_ty {
                    *bound
                } else {
                    NonZeroPow2Usize::next(elements.len().saturating_add(1))
                };

                let partition = Partition::from_slice(&nodes, bound.get() / 2);
                let process = |block: &[ProgNode]| -> ProgNode {
                    if block.is_empty() {
                        ProgNode::injl(ProgNode::unit())
                    } else {
                        let tree = BTreeSlice::from_slice(block);
                        let array = tree.fold(ProgNode::pair_unwrap);
                        ProgNode::injr(array)
                    }
                };

                partition.fold(process, ProgNode::pair_unwrap)
            }
        };
        if let Some(reqd_ty) = reqd_ty {
            expr.arrow()
                .target
                .unify(&reqd_ty.to_simplicity(), "")
                .map_err(|_| Error::TypeValueMismatch(reqd_ty.clone()))
                .with_span(span)?;
        }
        Ok(expr)
    }
}
