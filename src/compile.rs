//! Compile the parsed ast into a simplicity program

use std::{str::FromStr, sync::Arc};

use simplicity::{jet::Elements, node, Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::parse::{Pattern, SingleExpressionInner, UIntType};
use crate::{
    named::{ConstructExt, NamedConstructNode, ProgExt},
    parse::{Call, Expression, ExpressionInner, FunctionName, Program, Statement, Type},
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
        Statement::ClosureAssignment(assignment) => {
            scope.insert_closure(assignment.pattern.clone(), assignment.closure.clone());
            eval_blk(stmts, scope, index + 1, last_expr)
        }
        Statement::Call(func_call) => {
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

impl Call {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<&Type>) -> ProgNode {
        let args_expr = self
            .args
            .as_ref()
            .iter()
            .map(|e| e.eval(scope, None)) // TODO: Pass the jet source type here.
            .reduce(ProgNode::pair);

        match &self.name {
            FunctionName::Jet(jet_name) => {
                let jet = Elements::from_str(jet_name.as_inner()).expect("Invalid jet name");
                let jet = ProgNode::jet(jet);
                match args_expr {
                    Some(expr) => ProgNode::comp(expr, jet),
                    None => ProgNode::comp(ProgNode::unit(), jet),
                }
            }
            FunctionName::BuiltIn(..) => unimplemented!("Builtins are not supported yet"),
            FunctionName::UnwrapLeft => {
                debug_assert!(self.args.as_ref().len() == 1);
                let b = args_expr.unwrap();
                let left_and_unit = ProgNode::pair(b, ProgNode::unit());
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertl(take_iden, fail_cmr);
                ProgNode::comp(left_and_unit, get_inner)
            }
            FunctionName::UnwrapRight | FunctionName::Unwrap => {
                debug_assert!(self.args.as_ref().len() == 1);
                let c = args_expr.unwrap();
                let right_and_unit = ProgNode::pair(c, ProgNode::unit());
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertr(fail_cmr, take_iden);
                ProgNode::comp(right_and_unit, get_inner)
            }
            FunctionName::Closure(closure_name) => {
                // `let f = |a, b, c| e; f(1, 2, 3)`
                // is equivalent to
                // `{ let [a, b, c] = [1, 2, 3]; e }`
                scope.push_scope();

                let args_pattern = Pattern::Array(
                    scope
                        .get_closure(closure_name)
                        .args()
                        .as_ref()
                        .iter()
                        .cloned()
                        .map(Pattern::Identifier)
                        .collect(),
                );
                scope.insert(args_pattern);
                let args_expr = SingleExpressionInner::Array(self.args.clone().into());
                // TODO: Pass args type
                let args = args_expr.eval(scope, None);
                let closure_input = ProgNode::pair(args, ProgNode::iden());

                let closure_expr = scope.get_closure(closure_name).expr().clone();
                let closure_output = closure_expr.eval(scope, reqd_ty);

                scope.pop_scope();
                ProgNode::comp(closure_input, closure_output)
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
            ExpressionInner::SingleExpression(e) => e.inner.eval(scope, reqd_ty),
        }
    }
}

impl SingleExpressionInner {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<&Type>) -> ProgNode {
        let res = match self {
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
            SingleExpressionInner::Call(call) => call.eval(scope, reqd_ty),
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
            SingleExpressionInner::Array(elements) => {
                let el_type = if let Some(Type::Array(ty, _)) = reqd_ty {
                    Some(ty.as_ref())
                } else {
                    None
                };
                let nodes: Vec<_> = elements.iter().map(|e| e.eval(scope, el_type)).collect();
                let tree = BTreeSlice::from_slice(&nodes);
                tree.fold(ProgNode::pair)
            }
            SingleExpressionInner::List(elements) => {
                let el_type = if let Some(Type::List(ty, _)) = reqd_ty {
                    Some(ty.as_ref())
                } else {
                    None
                };
                let nodes: Vec<_> = elements.iter().map(|e| e.eval(scope, el_type)).collect();
                let bound = if let Some(Type::List(_, bound)) = reqd_ty {
                    *bound
                } else {
                    elements.len().next_power_of_two()
                };
                debug_assert!(bound.is_power_of_two());
                debug_assert!(2 <= bound);

                let partition = Partition::from_slice(&nodes, bound / 2);
                let process = |block: &[ProgNode]| -> ProgNode {
                    if block.is_empty() {
                        ProgNode::injl(ProgNode::unit())
                    } else {
                        let tree = BTreeSlice::from_slice(block);
                        let array = tree.fold(ProgNode::pair);
                        ProgNode::injr(array)
                    }
                };

                partition.fold(process, ProgNode::pair)
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
