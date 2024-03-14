//! Compile the parsed ast into a simplicity program

use std::{str::FromStr, sync::Arc};

use simplicity::{jet::Elements, node, Cmr, FailEntropy};

use crate::parse::{Pattern, SingleExpressionInner, UIntType};
use crate::{
    named::{ConstructExt, NamedConstructNode, ProgExt},
    parse::{
        Expression, ExpressionInner, FuncCall, FuncType, Program, SingleExpression, Statement, Type,
    },
    scope::GlobalScope,
    ProgNode,
};

fn eval_blk(
    stmts: &[Statement],
    scope: &mut GlobalScope,
    index: usize,
    last_expr: Option<&Expression>,
) -> ProgNode {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.eval(scope, None),
            None => Arc::new(NamedConstructNode::_new(node::Inner::Unit).unwrap()),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression.eval(scope, assignment.ty.as_ref());
            scope.insert(assignment.pattern.clone());
            let left = ProgNode::pair(expr, ProgNode::iden());
            let right = eval_blk(stmts, scope, index + 1, last_expr);
            ProgNode::comp(left, right)
        }
        Statement::FuncCall(func_call) => {
            let left = func_call.eval(scope, None);
            let right = eval_blk(stmts, scope, index + 1, last_expr);
            combine_seq(left, right)
        }
    }
}

fn combine_seq(a: ProgNode, b: ProgNode) -> ProgNode {
    let pair = ProgNode::pair(a, b);
    let drop_iden = ProgNode::drop_(ProgNode::iden());
    ProgNode::comp(pair, drop_iden)
}

impl Program {
    pub fn eval(&self, scope: &mut GlobalScope) -> ProgNode {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl FuncCall {
    pub fn eval(&self, scope: &mut GlobalScope, _reqd_ty: Option<&Type>) -> ProgNode {
        match &self.func_type {
            FuncType::Jet(jet_name) => {
                let args = self
                    .args
                    .iter()
                    .map(|e| e.eval(scope, None)) // TODO: Pass the jet source type here.
                    .reduce(ProgNode::pair);
                let jet = Elements::from_str(jet_name).expect("Invalid jet name");
                let jet = ProgNode::jet(jet);
                match args {
                    Some(param) => {
                        // println!("param: {}", param.arrow());
                        // println!("jet: {}", jet.arrow());
                        ProgNode::comp(param, jet)
                    }
                    None => ProgNode::comp(ProgNode::unit(), jet),
                }
            }
            FuncType::BuiltIn(..) => unimplemented!("Builtins are not supported yet"),
            FuncType::UnwrapLeft => {
                debug_assert!(self.args.len() == 1);
                let b = self.args[0].eval(scope, None);
                let left_and_unit = ProgNode::pair(b, ProgNode::unit());
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertl(take_iden, fail_cmr);
                ProgNode::comp(left_and_unit, get_inner)
            }
            FuncType::UnwrapRight | FuncType::Unwrap => {
                debug_assert!(self.args.len() == 1);
                let c = self.args[0].eval(scope, None);
                let right_and_unit = ProgNode::pair(c, ProgNode::unit());
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertr(fail_cmr, take_iden);
                ProgNode::comp(right_and_unit, get_inner)
            }
        }
    }
}

impl Expression {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<&Type>) -> ProgNode {
        match &self.inner {
            ExpressionInner::BlockExpression(stmts, expr) => {
                scope.push_scope();
                let res = eval_blk(stmts, scope, 0, Some(expr.as_ref()));
                scope.pop_scope();
                res
            }
            ExpressionInner::SingleExpression(e) => e.eval(scope, reqd_ty),
        }
    }
}

impl SingleExpression {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<&Type>) -> ProgNode {
        let res = match &self.inner {
            SingleExpressionInner::Unit => ProgNode::unit(),
            SingleExpressionInner::Left(l) => {
                let l = l.eval(scope, None);
                ProgNode::injl(l)
            }
            SingleExpressionInner::None => ProgNode::injl(ProgNode::unit()),
            SingleExpressionInner::Right(r) | SingleExpressionInner::Some(r) => {
                let r = r.eval(scope, None);
                ProgNode::injr(r)
            }
            SingleExpressionInner::False => ProgNode::injl(ProgNode::unit()),
            SingleExpressionInner::True => ProgNode::injr(ProgNode::unit()),
            SingleExpressionInner::Product(l, r) => {
                let l = l.eval(scope, None);
                let r = r.eval(scope, None);
                ProgNode::pair(l, r)
            }
            SingleExpressionInner::UnsignedInteger(decimal) => {
                let ty = reqd_ty
                    .unwrap_or(&Type::UInt(UIntType::U32))
                    .to_uint()
                    .expect("Not an integer type");
                let value = ty.parse_decimal(decimal);
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value))
            }
            SingleExpressionInner::BitString(bits) => {
                let value = bits.to_simplicity();
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value))
            }
            SingleExpressionInner::ByteString(bytes) => {
                let value = bytes.to_simplicity();
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value))
            }
            SingleExpressionInner::Witness(name) => {
                scope.insert_witness(name.clone());
                ProgNode::witness(name.as_inner().clone())
            }
            SingleExpressionInner::Variable(identifier) => {
                let res = scope.get(identifier);
                println!("Identifier {}: {}", identifier, res.arrow());
                res
            }
            SingleExpressionInner::FuncCall(call) => call.eval(scope, reqd_ty),
            SingleExpressionInner::Expression(expression) => expression.eval(scope, reqd_ty),
            SingleExpressionInner::Match {
                scrutinee,
                left,
                right,
            } => {
                let mut l_scope = scope.clone();
                if let Some(x) = left.pattern.get_identifier() {
                    l_scope.insert(Pattern::Identifier(x.clone()));
                }
                let l_compiled = left.expression.eval(&mut l_scope, reqd_ty);

                let mut r_scope = scope.clone();
                if let Some(y) = right.pattern.get_identifier() {
                    r_scope.insert(Pattern::Identifier(y.clone()));
                }
                let r_compiled = right.expression.eval(&mut r_scope, reqd_ty);

                // TODO: Enforce target type A + B for m_expr
                let scrutinized_input = scrutinee.eval(scope, None);
                let input = ProgNode::pair(scrutinized_input, ProgNode::iden());
                let output = ProgNode::case(l_compiled, r_compiled);
                ProgNode::comp(input, output)
            }
        };
        if let Some(reqd_ty) = reqd_ty {
            res.arrow()
                .target
                .unify(
                    &reqd_ty.to_simplicity(),
                    "Type mismatch for user provided type",
                )
                .unwrap();
        }
        res
    }
}
