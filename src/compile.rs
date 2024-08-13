//! Compile the parsed ast into a simplicity program

use std::sync::Arc;

use either::Either;
use simplicity::jet::Elements;
use simplicity::node::{CoreConstructible as _, JetConstructible as _};
use simplicity::{Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::ast::{
    Call, CallName, Expression, ExpressionInner, Match, Program, SingleExpression,
    SingleExpressionInner, Statement,
};
use crate::error::{Error, RichError, WithSpan};
use crate::named::{CoreExt, PairBuilder};
use crate::num::NonZeroPow2Usize;
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
    pub fn get(&self, target: &BasePattern) -> Option<PairBuilder<ProgNode>> {
        BasePattern::from(&self.get_input_pattern()).translate(target)
    }
}

fn compile_blk(
    stmts: &[Statement],
    scope: &mut Scope,
    index: usize,
    last_expr: Option<&Expression>,
) -> Result<PairBuilder<ProgNode>, RichError> {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.compile(scope),
            None => Ok(PairBuilder::unit()),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression().compile(scope)?;
            scope.insert(assignment.pattern().clone());
            let left = expr.pair(PairBuilder::iden());
            let right = compile_blk(stmts, scope, index + 1, last_expr)?;
            left.comp(&right).with_span(assignment)
        }
        Statement::Expression(expression) => {
            let left = expression.compile(scope)?;
            let right = compile_blk(stmts, scope, index + 1, last_expr)?;
            combine_seq(left, right).with_span(expression)
        }
    }
}

fn combine_seq(
    a: PairBuilder<ProgNode>,
    b: PairBuilder<ProgNode>,
) -> Result<PairBuilder<ProgNode>, simplicity::types::Error> {
    let pair = a.pair(b);
    let drop_iden = ProgNode::drop_(&ProgNode::iden());
    pair.comp(&drop_iden)
}

impl Program {
    pub fn compile(&self) -> Result<ProgNode, RichError> {
        let mut scope = Scope::new(Pattern::Ignore);
        self.main().compile(&mut scope).map(PairBuilder::build)
    }
}

impl Expression {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
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
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
        let expr = match self.inner() {
            SingleExpressionInner::Constant(value) => {
                // FIXME: Handle values that are not powers of two (requires updated rust-simplicity API)
                let value = StructuralValue::from(value);
                PairBuilder::unit_const_value(value.into())
            }
            SingleExpressionInner::Witness(name) => PairBuilder::witness(name.clone()),
            SingleExpressionInner::Variable(identifier) => scope
                .get(&BasePattern::Identifier(identifier.clone()))
                .ok_or(Error::UndefinedVariable(identifier.clone()))
                .with_span(self)?,
            SingleExpressionInner::Expression(expr) => expr.compile(scope)?,
            SingleExpressionInner::Tuple(elements) | SingleExpressionInner::Array(elements) => {
                let compiled = elements
                    .iter()
                    .map(|e| e.compile(scope))
                    .collect::<Result<Vec<PairBuilder<ProgNode>>, RichError>>()?;
                let tree = BTreeSlice::from_slice(&compiled);
                tree.fold(PairBuilder::pair)
                    .unwrap_or_else(PairBuilder::unit)
            }
            SingleExpressionInner::List(elements) => {
                let compiled = elements
                    .iter()
                    .map(|e| e.compile(scope))
                    .collect::<Result<Vec<PairBuilder<ProgNode>>, RichError>>()?;
                let bound = self.ty().as_list().unwrap().1;
                let partition = Partition::from_slice(&compiled, bound.get() / 2);
                partition.fold(
                    |block| {
                        let tree = BTreeSlice::from_slice(block);
                        match tree.fold(PairBuilder::pair) {
                            None => PairBuilder::unit().injl(),
                            Some(pair) => pair.injr(),
                        }
                    },
                    PairBuilder::pair,
                )
            }
            SingleExpressionInner::Option(None) => PairBuilder::unit().injl(),
            SingleExpressionInner::Either(Either::Left(inner)) => {
                inner.compile(scope).map(PairBuilder::injl)?
            }
            SingleExpressionInner::Either(Either::Right(inner))
            | SingleExpressionInner::Option(Some(inner)) => {
                inner.compile(scope).map(PairBuilder::injr)?
            }
            SingleExpressionInner::Call(call) => call.compile(scope)?,
            SingleExpressionInner::Match(match_) => match_.compile(scope)?,
        };

        expr.as_ref()
            .cached_data()
            .arrow()
            .target
            .unify(&StructuralType::from(self.ty()).to_unfinalized(), "")
            .map_err(|e| Error::CannotCompile(e.to_string()))
            .with_span(self)?;
        Ok(expr)
    }
}

impl Call {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
        let args_ast = SingleExpression::tuple(self.args().clone(), *self.as_ref());
        let args = args_ast.compile(scope)?;

        match self.name() {
            CallName::Jet(name) => {
                let jet = ProgNode::jet(*name);
                args.comp(&jet).with_span(self)
            }
            CallName::UnwrapLeft(..) => {
                let left_and_unit = args.pair(PairBuilder::unit());
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertl_take(&ProgNode::iden(), fail_cmr);
                left_and_unit.comp(&get_inner).with_span(self)
            }
            CallName::UnwrapRight(..) | CallName::Unwrap => {
                let right_and_unit = args.pair(PairBuilder::unit());
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertr_take(fail_cmr, &ProgNode::iden());
                right_and_unit.comp(&get_inner).with_span(self)
            }
            CallName::IsNone(..) => {
                let sum_and_unit = args.pair(PairBuilder::unit());
                let is_right = ProgNode::case_true_false();
                sum_and_unit.comp(&is_right).with_span(self)
            }
            CallName::Assert => {
                let jet = ProgNode::jet(Elements::Verify);
                args.comp(&jet).with_span(self)
            }
            CallName::Panic => {
                // panic! ignores its arguments
                Ok(PairBuilder::fail(FailEntropy::ZERO))
            }
            CallName::TypeCast(..) => {
                // A cast converts between two structurally equal types.
                // Structural equality of Simfony types A and B means
                // exact equality of the underlying Simplicity types of A and of B.
                // Therefore, a Simfony cast is a NOP in Simplicity.
                Ok(args)
            }
            CallName::Custom(function) => {
                let mut function_scope = Scope::new(function.params_pattern());
                let body = function.body().compile(&mut function_scope)?;
                args.comp(&body).with_span(self)
            }
            CallName::Fold(function, bound) => {
                let mut function_scope = Scope::new(function.params_pattern());
                let body = function.body().compile(&mut function_scope)?;
                let fold_body = list_fold(*bound, body.as_ref()).with_span(self)?;
                args.comp(&fold_body).with_span(self)
            }
            CallName::ForWhile(..) => todo!(),
        }
    }
}

/// Fold a list of less than `2^n` elements using function `f`.
///
/// Function `f: E × A → A`
/// takes a list element of type `E` and an accumulator of type `A`,
/// and it produces an updated accumulator of type `A`.
///
/// The fold `(fold f)_n : E^(<2^n) × A → A`
/// takes the list of type `E^(<2^n)` and an initial accumulator of type `A`,
/// and it produces the final accumulator of type `A`.
fn list_fold(bound: NonZeroPow2Usize, f: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
    /* f_0 :  E × A → A
     * f_0 := f
     */
    let mut f_array = f.clone();

    /* (fold f)_1 :  E^<2 × A → A
     * (fold f)_1 := case IH f_0
     */
    let ioh = ProgNode::i().h();
    let mut f_fold = ProgNode::case(ioh.as_ref(), &f_array)?;
    let mut i = NonZeroPow2Usize::TWO;

    fn next_f_array(f_array: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
        /* f_(n + 1) :  E^(2^(n + 1)) × A → A
         * f_(n + 1) := OIH ▵ (OOH ▵ IH; f_n); f_n
         */
        let half1_acc = ProgNode::o().o().h().pair(ProgNode::i().h());
        let updated_acc = half1_acc.comp(f_array)?;
        let half2_acc = ProgNode::o().i().h().pair(updated_acc);
        half2_acc.comp(f_array).map(PairBuilder::build)
    }
    fn next_f_fold(
        f_array: &ProgNode,
        f_fold: &ProgNode,
    ) -> Result<ProgNode, simplicity::types::Error> {
        /* (fold f)_(n + 1) :  E<2^(n + 1) × A → A
         * (fold f)_(n + 1) := OOH ▵ (OIH ▵ IH);
         *                     case (drop (fold f)_n)
         *                          ((IOH ▵ (OH ▵ IIH; f_n)); (fold f)_n)
         */
        let case_input = ProgNode::o()
            .o()
            .h()
            .pair(ProgNode::o().i().h().pair(ProgNode::i().h()));
        let case_left = ProgNode::drop_(f_fold);

        let f_n_input = ProgNode::o().h().pair(ProgNode::i().i().h());
        let f_n_output = f_n_input.comp(f_array)?;
        let fold_n_input = ProgNode::i().o().h().pair(f_n_output);
        let case_right = fold_n_input.comp(f_fold)?;

        case_input
            .comp(&ProgNode::case(&case_left, case_right.as_ref())?)
            .map(PairBuilder::build)
    }

    while i < bound {
        f_array = next_f_array(&f_array)?;
        f_fold = next_f_fold(&f_array, &f_fold)?;
        i = i.mul2();
    }

    Ok(f_fold)
}

impl Match {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
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
        let input = scrutinee.pair(PairBuilder::iden());
        let output = ProgNode::case(left.as_ref(), right.as_ref()).with_span(self)?;
        input.comp(&output).with_span(self)
    }
}
