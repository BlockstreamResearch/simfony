//! Compile the parsed ast into a simplicity program

use std::str::FromStr;

use simplicity::{
    jet::Elements,
    node::{self, CoreConstructible, JetConstructible, WitnessConstructible},
    FailEntropy, Value,
};

use crate::{
    parse::{
        Constants, Expression, FuncCall, FuncType, Program, SingleExpression, Statement, Term, Type,
    },
    scope::{GlobalScope, Variable},
    ProgNode,
};

fn eval_blk(
    stmts: &[Statement],
    scope: &mut GlobalScope,
    index: usize,
    last_expr: Option<&Box<Expression>>,
) -> ProgNode {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.eval(scope, None),
            None => ProgNode::unit(),
        };
    }
    let res = match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression.eval(scope, assignment.ty);
            scope.insert(Variable::Single(assignment.identifier.clone()));
            let left = ProgNode::pair(&expr, &ProgNode::iden()).expect("TYPECHECK: must succeed.");
            let right = eval_blk(stmts, scope, index + 1, last_expr);
            println!("l:{} r:{} index:{index}", &left.arrow(), &right.arrow());
            ProgNode::comp(&left, &right).expect(&format!(
                "Assignments must be of unit target type {index} {}",
                &assignment.identifier
            ))
        }
        Statement::WitnessDecl(witness_ident) => {
            // let _witness = ProgNode::witness(node::NoWitness);
            scope.insert_witness(witness_ident.to_string());
            eval_blk(stmts, scope, index + 1, last_expr)
        }
        Statement::FuncCall(func_call) => {
            let left = func_call.eval(scope, None);
            let right = eval_blk(stmts, scope, index + 1, last_expr);
            combine_seq(&left, &right)
        }
        Statement::DestructTuple(tuple) => {
            let expr = tuple.expression.eval(scope, tuple.ty);
            scope.insert(Variable::Tuple(
                tuple.l_ident.clone(),
                tuple.r_ident.clone(),
            ));
            let left = ProgNode::pair(&expr, &ProgNode::iden()).expect("TYPECHECK: must succeed.");

            let right = eval_blk(stmts, scope, index + 1, last_expr);
            ProgNode::comp(&left, &right)
                .expect(&format!("Assignments must be of unit target type {index}"))
        }
    };
    res
}

fn combine_seq(a: &ProgNode, b: &ProgNode) -> ProgNode {
    let pair = ProgNode::pair(a, b).expect("Pair creation error");
    let drop_iden = ProgNode::drop_(&ProgNode::iden());
    ProgNode::comp(&pair, &drop_iden)
        .expect("Improve this error. func calls must be of unit target type")
}

impl Program {
    pub fn eval(&self, scope: &mut GlobalScope) -> ProgNode {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl FuncCall {
    pub fn eval(&self, scope: &mut GlobalScope, _reqd_ty: Option<Type>) -> ProgNode {
        match &self.func_name {
            FuncType::Jet(jet_name) => {
                let args = self
                    .args
                    .iter()
                    .map(|e| e.eval(scope, None)) // TODO: Pass the jet source type here.
                    .reduce(|acc, e| {
                        ProgNode::pair(&acc, &e).expect("Function arg creation error")
                    });
                let jet = Elements::from_str(&jet_name).expect("Invalid jet name");
                let jet = ProgNode::jet(jet);
                match args {
                    Some(param) => {
                        println!("param: {}", param.arrow());
                        println!("jet: {}", jet.arrow());
                        ProgNode::comp(&param, &jet)
                            .expect("Improve this error. func calls must have correct arguments")
                    }
                    None => ProgNode::comp(&ProgNode::unit(), &jet)
                        .expect("Improve this error. func calls must have correct arguments"),
                }
            }
            FuncType::BuiltIn(f_name) => {
                // binary builtins
                if self.args.len() != 1 {
                    panic!("Only unary builtins supported");
                }
                let left = self.args[0].eval(scope, None);
                match f_name.as_str() {
                    "not" => {
                        let res = ProgNode::not(&left).expect("TYPECHECK: and typecheck");
                        println!("not: {}", res.arrow());
                        res
                    }
                    _ => panic!("Unknown builtin function"),
                }
            }
            FuncType::AssertL => {
                debug_assert!(self.args.len() == 1);
                let e1 = self.args[0].eval(scope, None);
                let fail_entropy = FailEntropy::from_byte_array([0; 64]);
                println!("left: {}", e1.arrow());
                let e1 = ProgNode::pair(&e1, &ProgNode::unit()).expect("TYPECHECK: and typecheck");
                let res = ProgNode::case(&ProgNode::iden(), &ProgNode::fail(fail_entropy))
                    .expect("TYPECHECK: and typecheck");
                println!("assert_l: {} target {:?}", res.arrow(), res.arrow().target);
                let res = ProgNode::comp(&e1, &res).unwrap();
                println!("assert_l: {}", res.arrow());
                let res = ProgNode::comp(&res, &ProgNode::take(&ProgNode::iden())).unwrap();
                println!("assert_l: {}", res.arrow());
                res
            }
            FuncType::AssertR => {
                // comp (assertr cmrFail0 (pair ⟦e1⟧Ξ iden))
                debug_assert!(self.args.len() == 1);
                let e1 = self.args[0].eval(scope, None);
                // let pair_e1_iden = ProgNode::pair(&e1, &ProgNode::iden()).unwrap();
                let fail_entropy = FailEntropy::from_byte_array([0; 64]);
                let e1 = ProgNode::pair(&e1, &ProgNode::unit()).expect("TYPECHECK: and typecheck");
                println!("e1: {}", e1.arrow());
                let res = ProgNode::case(&ProgNode::fail(fail_entropy), &ProgNode::iden())
                    .expect("TYPECHECK: and typecheck");
                println!("assert_r: {}", res.arrow());
                let res = ProgNode::comp(&e1, &res).unwrap();
                println!("assert_r: {}", res.arrow());
                let res = ProgNode::comp(&res, &ProgNode::take(&ProgNode::iden())).unwrap();
                println!("assert_r: {}", res.arrow());
                res
            }
        }
    }
}

impl Expression {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<Type>) -> ProgNode {
        match self {
            Expression::BlockExpression(stmts, expr) => {
                scope.push_scope();
                let res = eval_blk(stmts, scope, 0, Some(expr));
                scope.pop_scope();
                res
            }
            Expression::Pair(e1, e2) => {
                ProgNode::pair(&e1.eval(scope, None), &e2.eval(scope, None)).expect("Pair error")
            }
            Expression::SingleExpression(e) => e.eval(scope, reqd_ty),
        }
    }
}

impl SingleExpression {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<Type>) -> ProgNode {
        let res = match self {
            SingleExpression::Term(term) => term.eval(scope, reqd_ty),
        };
        if let Some(reqd_ty) = reqd_ty {
            res.arrow()
                .target
                .unify(
                    &reqd_ty.to_simplicity_type(),
                    "Type mismatch for user provided type",
                )
                .unwrap();
        }
        res
    }
}

fn assert_type(reqd_ty: Option<Type>, actual_ty: Type) {
    if let Some(reqd_ty) = reqd_ty {
        if reqd_ty != actual_ty {
            panic!(
                "Type mismatch. Expected {:?} but got {:?}",
                reqd_ty, actual_ty
            );
        }
    }
}

impl Term {
    pub fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<Type>) -> ProgNode {
        let res = match self {
            Term::Constants(constants) => match constants {
                Constants::None => todo!("None type here"),
                Constants::False => {
                    let _false = Value::u1(0);
                    assert_type(reqd_ty, Type::U1);
                    ProgNode::const_word(_false)
                }
                Constants::True => {
                    let _true = Value::u1(1);
                    assert_type(reqd_ty, Type::U1);
                    ProgNode::const_word(_true)
                }
                Constants::Number(number) => {
                    let v = if let Some(ty) = reqd_ty {
                        ty.parse_num(number)
                    } else {
                        let num = number.parse::<u32>().unwrap();
                        Value::u32(num)
                    };
                    ProgNode::comp(&ProgNode::unit(), &ProgNode::const_word(v))
                        .expect("Const word have source type one")
                }
                Constants::Unit => ProgNode::unit(),
            },
            Term::Witness(_witness) => ProgNode::witness(node::NoWitness),
            Term::FuncCall(func_call) => func_call.eval(scope, reqd_ty),
            Term::Identifier(identifier) => {
                let res = scope.get(identifier);
                println!("Identifier {}: {}", identifier, res.arrow());
                res
            }
            Term::Expression(expression) => expression.eval(scope, reqd_ty),
        };
        if let Some(reqd_ty) = reqd_ty {
            res.arrow()
                .target
                .unify(
                    &reqd_ty.to_simplicity_type(),
                    "Type mismatch for user provided type",
                )
                .unwrap();
        }
        res
    }
}
