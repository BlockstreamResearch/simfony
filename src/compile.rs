//! Compile the parsed ast into a simplicity program

use std::sync::Arc;

use either::Either;
use simplicity::jet::Elements;
use simplicity::node::{CoreConstructible as _, JetConstructible as _, WitnessConstructible as _};
use simplicity::{Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::ast::{
    Call, CallName, Expression, ExpressionInner, FunctionParam, Match, Program, SingleExpression,
    SingleExpressionInner, Statement,
};
use crate::error::{Error, RichError, WithSpan};
use crate::named::CoreExt;
use crate::pattern::{BasePattern, Pattern};
use crate::types::{StructuralType, TypeDeconstructible};
use crate::value::StructuralValue;
use crate::ProgNode;

/// Each Simfony expression expects an _input value_.
/// A Simfony expression is translated into a Simplicity expression
/// that similarly expects an _input value_.
///
/// Simfony variable names are translated into Simplicity expressions
/// that extract the seeked value from the _input value_.
///
/// Each (nested) block expression introduces a new scope.
/// Bindings from inner scopes overwrite bindings from outer scopes.
/// Bindings live as long as their scope.
#[derive(Debug, Clone)]
struct Scope {
    /// For each scope, the set of assigned variables.
    ///
    /// A stack of scopes. Each scope is a stack of patterns.
    /// New patterns are pushed onto the top _(current, innermost)_ scope.
    ///
    /// ## Input pattern
    ///
    /// The stack of scopes corresponds to an _input pattern_.
    /// All valid input values match the input pattern.
    ///
    /// ## Example
    ///
    /// The stack `[[p1], [p2, p3]]` corresponds to a nested product pattern:
    ///
    /// ```text
    ///    .
    ///   / \
    /// p3   .
    ///     / \
    ///   p2   p1
    /// ```
    ///
    /// Inner scopes occur higher in the tree than outer scopes.
    /// Later assignments occur higher in the tree than earlier assignments.
    /// ```
    variables: Vec<Vec<Pattern>>,
}

impl Scope {
    /// Create a new [`Scope`] for an `input` value that matches the pattern.
    pub fn new(input: Pattern) -> Self {
        Self {
            variables: vec![vec![input]],
        }
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(Vec::new());
    }

    /// Pop the current scope from the stack.
    ///
    /// # Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Empty stack");
    }

    /// Push an assignment to the current scope.
    ///
    /// Update the input pattern accordingly:
    ///
    /// ```text
    ///   .
    ///  / \
    /// p   previous
    /// ```
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert(&mut self, pattern: Pattern) {
        self.variables
            .last_mut()
            .expect("Empty stack")
            .push(pattern);
    }

    /// Get the input pattern.
    ///
    /// All valid input values match the input pattern.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    fn get_input_pattern(&self) -> Pattern {
        let mut it = self.variables.iter().flat_map(|scope| scope.iter());
        let first = it.next().expect("Empty stack");
        it.cloned()
            .fold(first.clone(), |acc, next| Pattern::product(next, acc))
    }

    /// Compute a Simplicity expression that takes a valid input value (that matches the input pattern)
    /// and that produces as output a value that matches the `target` pattern.
    ///
    /// ## Example
    ///
    /// ```
    /// let a: u8 = 0;
    /// let b = {
    ///     let b: u8 = 1;
    ///     let c: u8 = 2;
    ///     (a, b)  // here we seek the value of `(a, b)`
    /// };
    /// ```
    ///
    /// The input pattern looks like this:
    ///
    /// ```text
    ///   .
    ///  / \
    /// c   .
    ///    / \
    ///   b   .
    ///      / \
    ///     a   _
    /// ```
    ///
    /// The expression `drop (IOH & OH)` returns the seeked value.
    pub fn get(&self, target: &BasePattern) -> Option<ProgNode> {
        BasePattern::from(&self.get_input_pattern()).translate(target)
    }
}

fn compile_blk(
    stmts: &[Statement],
    scope: &mut Scope,
    index: usize,
    last_expr: Option<&Expression>,
) -> Result<ProgNode, RichError> {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.compile(scope),
            None => Ok(ProgNode::unit()),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression().compile(scope)?;
            scope.insert(assignment.pattern().clone());
            let left = ProgNode::pair_iden(&expr);
            let right = compile_blk(stmts, scope, index + 1, last_expr)?;
            ProgNode::comp(&left, &right).with_span(assignment)
        }
        Statement::Expression(expression) => {
            let left = expression.compile(scope)?;
            let right = compile_blk(stmts, scope, index + 1, last_expr)?;
            combine_seq(&left, &right).with_span(expression)
        }
    }
}

fn combine_seq(a: &ProgNode, b: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
    let pair = ProgNode::pair(a, b)?;
    let drop_iden = ProgNode::drop_(&ProgNode::iden());
    ProgNode::comp(&pair, &drop_iden)
}

impl Program {
    pub fn compile(&self) -> Result<ProgNode, RichError> {
        let mut scope = Scope::new(Pattern::Ignore);
        self.main().compile(&mut scope)
    }
}

impl Expression {
    fn compile(&self, scope: &mut Scope) -> Result<ProgNode, RichError> {
        match self.inner() {
            ExpressionInner::Block(stmts, expr) => {
                scope.push_scope();
                let res = compile_blk(stmts, scope, 0, expr.as_ref().map(Arc::as_ref));
                scope.pop_scope();
                res
            }
            ExpressionInner::Single(e) => e.compile(scope),
        }
    }
}

impl SingleExpression {
    fn compile(&self, scope: &mut Scope) -> Result<ProgNode, RichError> {
        let expr = match self.inner() {
            SingleExpressionInner::Constant(value) => {
                // FIXME: Handle values that are not powers of two (requires updated rust-simplicity API)
                let value = StructuralValue::from(value);
                ProgNode::unit_comp(&ProgNode::const_word(value.into()))
            }
            SingleExpressionInner::Witness(name) => ProgNode::witness(name.clone()),
            SingleExpressionInner::Variable(identifier) => scope
                .get(&BasePattern::Identifier(identifier.clone()))
                .ok_or(Error::UndefinedVariable(identifier.clone()))
                .with_span(self)?,
            SingleExpressionInner::Expression(expr) => expr.compile(scope)?,
            SingleExpressionInner::Tuple(elements) | SingleExpressionInner::Array(elements) => {
                let compiled = elements
                    .iter()
                    .map(|e| e.compile(scope))
                    .collect::<Vec<Result<ProgNode, RichError>>>();
                let tree = BTreeSlice::from_slice(&compiled);
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                tree.fold(|res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(self)))
                })
                .unwrap_or_else(|| Ok(ProgNode::unit()))?
            }
            SingleExpressionInner::List(elements) => {
                let compiled = elements
                    .iter()
                    .map(|e| e.compile(scope))
                    .collect::<Vec<Result<ProgNode, RichError>>>();
                let bound = self.ty().as_list().unwrap().1;
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let partition = Partition::from_slice(&compiled, bound.get() / 2);
                let process =
                    |block: &[Result<ProgNode, RichError>]| -> Result<ProgNode, RichError> {
                        let tree = BTreeSlice::from_slice(block);
                        tree.fold(|res_a, res_b| {
                            res_a.and_then(|a| {
                                res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(self))
                            })
                        })
                        .map(|res| res.map(|array| ProgNode::injr(&array)))
                        .unwrap_or_else(|| Ok(ProgNode::bit_false()))
                    };

                partition.fold(process, |res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(self)))
                })?
            }
            SingleExpressionInner::Option(None) => ProgNode::injl(&ProgNode::unit()),
            SingleExpressionInner::Either(Either::Left(inner)) => {
                let compiled = inner.compile(scope)?;
                ProgNode::injl(&compiled)
            }
            SingleExpressionInner::Either(Either::Right(inner))
            | SingleExpressionInner::Option(Some(inner)) => {
                let compiled = inner.compile(scope)?;
                ProgNode::injr(&compiled)
            }
            SingleExpressionInner::Call(call) => call.compile(scope)?,
            SingleExpressionInner::Match(match_) => match_.compile(scope)?,
        };

        expr.cached_data()
            .arrow()
            .target
            .unify(&StructuralType::from(self.ty()).to_unfinalized(), "")
            .map_err(|e| Error::CannotCompile(e.to_string()))
            .with_span(self)?;
        Ok(expr)
    }
}

impl Call {
    fn compile(&self, scope: &mut Scope) -> Result<ProgNode, RichError> {
        let args_ast = SingleExpression::tuple(self.args().clone(), *self.as_ref());
        let args = args_ast.compile(scope)?;

        match self.name() {
            CallName::Jet(name) => {
                let jet = ProgNode::jet(*name);
                ProgNode::comp(&args, &jet).with_span(self)
            }
            CallName::UnwrapLeft(..) => {
                let left_and_unit = ProgNode::pair_unit(&args);
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertl_take(&ProgNode::iden(), fail_cmr);
                ProgNode::comp(&left_and_unit, &get_inner).with_span(self)
            }
            CallName::UnwrapRight(..) | CallName::Unwrap => {
                let right_and_unit = ProgNode::pair_unit(&args);
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertr_take(fail_cmr, &ProgNode::iden());
                ProgNode::comp(&right_and_unit, &get_inner).with_span(self)
            }
            CallName::IsNone(..) => {
                let sum_and_unit = ProgNode::pair_unit(&args);
                let is_right = ProgNode::case_true_false();
                ProgNode::comp(&sum_and_unit, &is_right).with_span(self)
            }
            CallName::Assert => {
                let jet = ProgNode::jet(Elements::Verify);
                ProgNode::comp(&args, &jet).with_span(self)
            }
            CallName::Panic => {
                // panic! ignores its arguments
                Ok(ProgNode::fail(FailEntropy::ZERO))
            }
            CallName::TypeCast(..) => {
                // A cast converts between two structurally equal types.
                // Structural equality of Simfony types A and B means
                // exact equality of the underlying Simplicity types of A and of B.
                // Therefore, a Simfony cast is a NOP in Simplicity.
                Ok(args)
            }
            CallName::Custom(function) => {
                let params_pattern = Pattern::tuple(
                    function
                        .params()
                        .iter()
                        .map(FunctionParam::identifier)
                        .cloned()
                        .map(Pattern::Identifier),
                );
                let mut function_scope = Scope::new(params_pattern);
                let body = function.body().compile(&mut function_scope)?;
                ProgNode::comp(&args, &body).with_span(self)
            }
        }
    }
}

impl Match {
    fn compile(&self, scope: &mut Scope) -> Result<ProgNode, RichError> {
        scope.push_scope();
        scope.insert(
            self.left()
                .pattern()
                .as_variable()
                .cloned()
                .map(Pattern::Identifier)
                .unwrap_or(Pattern::Ignore),
        );
        let left = self.left().expression().compile(scope)?;
        scope.pop_scope();

        scope.push_scope();
        scope.insert(
            self.right()
                .pattern()
                .as_variable()
                .cloned()
                .map(Pattern::Identifier)
                .unwrap_or(Pattern::Ignore),
        );
        let right = self.right().expression().compile(scope)?;
        scope.pop_scope();

        let scrutinee = self.scrutinee().compile(scope)?;
        let input = ProgNode::pair_iden(&scrutinee);
        let output = ProgNode::case(&left, &right).with_span(self)?;
        ProgNode::comp(&input, &output).with_span(self)
    }
}
