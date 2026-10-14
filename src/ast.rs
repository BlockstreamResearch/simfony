mod analyze;
mod jet_hinter;
mod recovery;
mod scope;
#[cfg(test)]
mod tests;

pub use self::jet_hinter::{CoreJetHinter, ElementsJetHinter, JetHinter};

use std::num::NonZeroUsize;
use std::sync::Arc;

use either::Either;
use miniscript::iter::{Tree, TreeLike};

use crate::compile::RawHashJets;
use crate::debug::{CallTracker, DebugSymbols};
use crate::error::Span;
use crate::impl_eq_hash;
use crate::jet::JetHL;
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::parse::MatchPattern;
use crate::pattern::Pattern;
use crate::str::Identifier;
use crate::types::{ResolvedType, TypeConstructible};
use crate::value::Value;
use crate::witness::{Parameters, WitnessTypes};
use crate::TemplateProgramWitness;

/// A program consists of the main function.
///
/// Other items such as custom functions or type aliases
/// are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    main: Expression,
    parameters: Parameters,
    witness_types: WitnessTypes,
    call_tracker: Arc<CallTracker>,
}

impl Program {
    /// Access the main function.
    ///
    /// There is exactly one main function for each program.
    pub fn main(&self) -> &Expression {
        &self.main
    }

    /// Access the parameters of the program.
    pub fn parameters(&self) -> &Parameters {
        &self.parameters
    }

    /// Access the witness types of the program.
    pub fn witness_types(&self) -> &WitnessTypes {
        &self.witness_types
    }

    /// Access the debug symbols of the program.
    pub fn debug_symbols(&self, file: &str) -> DebugSymbols {
        self.call_tracker.with_file(file)
    }

    /// Access the tracker of function calls.
    pub(crate) fn call_tracker(&self) -> &Arc<CallTracker> {
        &self.call_tracker
    }
}

/// An item is a component of a program.
///
/// All items except for the main function are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Item {
    /// A type alias.
    ///
    /// A stub because the alias was resolved during the creation of the AST.
    TypeAlias,
    /// An enum declaration.
    ///
    /// A stub because the declaration was resolved into scope during the
    /// creation of the AST.
    EnumDeclaration,
    /// A function.
    Function(Function),
    Use,
    Module(Vec<Item>),
    /// A placeholder used for error recovery during parsing.
    Ignored,
}

/// Definition of a function.
///
/// All functions except for the main function are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Function {
    /// A custom function.
    ///
    /// A stub because the definition of the function was moved to its calls in the main function.
    Custom,
    /// The main function.
    ///
    /// An expression that takes no inputs (unit) and that produces no output (unit).
    /// The expression may panic midway through, signalling failure.
    /// Otherwise, the expression signals success.
    ///
    /// This expression is evaluated when the program is run.
    Main(Expression),
}

/// A statement is a component of a block expression.
///
/// Statements can define variables or run validating expressions,
/// but they never return values.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// Variable assignment.
    Assignment(Assignment),
    /// Expression that returns nothing (the unit value).
    Expression(Expression),
}

/// Assignment of a value to a variable identifier.
#[derive(Clone, Debug)]
pub struct Assignment {
    pattern: Pattern,
    expression: Expression,
    span: Span,
}

impl Assignment {
    /// Access the pattern of the assignment.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Access the expression of the assignment.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the span of the assignment.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Assignment; pattern, expression);

/// An expression returns a value.
#[derive(Clone, Debug)]
pub struct Expression {
    inner: ExpressionInner,
    ty: ResolvedType,
    span: Span,
}

impl_eq_hash!(Expression; inner, ty);

impl Expression {
    /// Access the inner expression.
    pub fn inner(&self) -> &ExpressionInner {
        &self.inner
    }

    /// Access the type of the expression.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

/// Variant of an expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionInner {
    /// A single expression directly returns a value.
    Single(SingleExpression),
    /// A block expression first executes a series of statements inside a local scope.
    /// Then, the block returns the value of its final expression.
    /// The block returns nothing (unit) if there is no final expression.
    Block(Arc<[Statement]>, Option<Arc<Expression>>),
}

/// A single expression directly returns its value.
#[derive(Clone, Debug)]
pub struct SingleExpression {
    inner: SingleExpressionInner,
    ty: ResolvedType,
    span: Span,
}

impl SingleExpression {
    /// Create a tuple expression from the given arguments and span.
    pub fn tuple(args: Arc<[Expression]>, span: Span) -> Self {
        let ty = ResolvedType::tuple(
            args.iter()
                .map(Expression::ty)
                .cloned()
                .collect::<Vec<ResolvedType>>(),
        );
        let inner = SingleExpressionInner::Tuple(args);
        Self { inner, ty, span }
    }

    /// Access the inner expression.
    pub fn inner(&self) -> &SingleExpressionInner {
        &self.inner
    }

    /// Access the type of the expression.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(SingleExpression; inner, ty);

/// Variant of a single expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SingleExpressionInner {
    /// Constant value.
    Constant(Value),
    /// Witness value.
    Witness(TemplateProgramWitness),
    /// Parameter value.
    Parameter(TemplateProgramWitness),
    /// Variable that has been assigned a value.
    Variable(Identifier),
    /// Expression in parentheses.
    Expression(Arc<Expression>),
    /// Tuple expression.
    Tuple(Arc<[Expression]>),
    /// Array expression.
    Array(Arc<[Expression]>),
    /// Bounded list of expressions.
    List(Arc<[Expression]>),
    /// Either expression.
    Either(Either<Arc<Expression>, Arc<Expression>>),
    /// Option expression.
    Option(Option<Arc<Expression>>),
    /// Call expression.
    Call(Call),
    /// Match expression.
    Match(Match),
    /// Match expression over an enum's variants.
    EnumMatch(EnumMatch),
    /// Construction of an enum variant.
    ///
    /// The enum's definition lives in the type of the expression.
    EnumConstruction(EnumConstruction),
}

/// Call of a user-defined or of a builtin function.
#[derive(Clone, Debug)]
pub struct Call {
    name: CallName,
    args: Arc<[Expression]>,
    span: Span,
}

impl Call {
    /// Access the name of the call.
    pub fn name(&self) -> &CallName {
        &self.name
    }

    /// Access the arguments of the call.
    pub fn args(&self) -> &Arc<[Expression]> {
        &self.args
    }

    /// Access the span of the call.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Call; name, args);

/// Name of a called function.
#[derive(Clone, Debug, Eq, Hash)]
#[allow(clippy::derived_hash_with_manual_eq)] // see comment on manual `PartialEq` impl below
pub enum CallName {
    /// Jet type.
    Jet(Box<dyn JetHL>),
    /// [`Either::unwrap_left`].
    UnwrapLeft(ResolvedType),
    /// [`Either::unwrap_right`].
    UnwrapRight(ResolvedType),
    /// [`Option::is_none`].
    IsNone(ResolvedType),
    /// [`Option::unwrap`].
    Unwrap,
    /// [`assert!`].
    Assert,
    /// [`panic!`] without error message.
    Panic,
    /// [`dbg!`].
    Debug,
    /// Cast from the given source type.
    TypeCast(ResolvedType),
    /// A custom function that was defined previously.
    ///
    /// We effectively copy the function body into every call of the function.
    /// We use [`Arc`] for cheap clones during this process.
    Custom(CustomFunction),
    /// Fold of a bounded list with the given function.
    Fold(CustomFunction, NonZeroPow2Usize),
    /// Fold of an array with the given function.
    ArrayFold(CustomFunction, NonZeroUsize),
    /// Loop over the given function a bounded number of times until it returns success.
    ForWhile(CustomFunction, Pow2Usize),
    /// SHA-256 of the concatenated bytes of a tuple of unsigned integers of the given type,
    /// using the given jets.
    RawHash(ResolvedType, RawHashJets),
}

// Manually implemented because the 1.74 (MSRV) derive expands to a body that
// moves out of the non-Copy `Box<dyn Jet>` field, later rustc versions are
// fine.
impl PartialEq for CallName {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Jet(a), Self::Jet(b)) => a == b,
            (Self::UnwrapLeft(a), Self::UnwrapLeft(b)) => a == b,
            (Self::UnwrapRight(a), Self::UnwrapRight(b)) => a == b,
            (Self::IsNone(a), Self::IsNone(b)) => a == b,
            (Self::Unwrap, Self::Unwrap) => true,
            (Self::Assert, Self::Assert) => true,
            (Self::Panic, Self::Panic) => true,
            (Self::Debug, Self::Debug) => true,
            (Self::TypeCast(a), Self::TypeCast(b)) => a == b,
            (Self::Custom(a), Self::Custom(b)) => a == b,
            (Self::Fold(a, b), Self::Fold(c, d)) => a == c && b == d,
            (Self::ArrayFold(a, b), Self::ArrayFold(c, d)) => a == c && b == d,
            (Self::ForWhile(a, b), Self::ForWhile(c, d)) => a == c && b == d,
            (Self::RawHash(a, b), Self::RawHash(c, d)) => a == c && b == d,
            _ => false,
        }
    }
}

/// Definition of a custom function.
#[derive(Clone, Debug)]
pub struct CustomFunction {
    params: Arc<[FunctionParam]>,
    ret: ResolvedType,
    /// `None` if the analysis of the body failed.
    body: Option<Arc<Expression>>,
    span: Span,
}

impl CustomFunction {
    /// Access the identifiers of the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the declared return type of the function.
    pub fn ret(&self) -> &ResolvedType {
        &self.ret
    }

    /// Access the body of the function.
    ///
    /// ## Panics
    ///
    /// Panics if the analysis of the body failed. This cannot happen for a function
    /// of an analyzed [`Program`], because a program with errors is never built.
    pub fn body(&self) -> &Expression {
        self.analyzed_body()
            .expect("programs with errors are never built")
    }

    /// Access the body of the function, if its analysis succeeded.
    fn analyzed_body(&self) -> Option<&Expression> {
        self.body.as_deref()
    }

    /// Access the span of the complete function declaration.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Return a pattern for the parameters of the function.
    pub fn params_pattern(&self) -> Pattern {
        Pattern::tuple(
            self.params()
                .iter()
                .map(FunctionParam::identifier)
                .cloned()
                .map(Pattern::Identifier),
        )
    }
}

impl_eq_hash!(CustomFunction; params, ret, analyzed_body);

/// Parameter of a function.
#[derive(Clone, Debug)]
pub struct FunctionParam {
    identifier: Identifier,
    ty: ResolvedType,
    span: Span,
}

impl FunctionParam {
    /// Access the identifier of the parameter.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// Access the type of the parameter.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
    }

    /// Access the span of the complete parameter declaration.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(FunctionParam; identifier, ty);

/// Match expression.
#[derive(Clone, Debug)]
pub struct Match {
    scrutinee: Arc<Expression>,
    left: MatchArm,
    right: MatchArm,
    span: Span,
}

impl Match {
    /// Access the expression whose output is destructed in the match statement.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the branch that handles structural left values.
    pub fn left(&self) -> &MatchArm {
        &self.left
    }

    /// Access the branch that handles structural right values.
    pub fn right(&self) -> &MatchArm {
        &self.right
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Match; scrutinee, left, right);

/// Match expression over an enum's variants.
#[derive(Clone, Debug)]
pub struct EnumMatch {
    scrutinee: Arc<Expression>,
    /// Arms in variant order (declaration order).
    ///
    /// The order matches the leaf order of the enum's balanced sum.
    arms: Arc<[EnumMatchArm]>,
    span: Span,
}

impl EnumMatch {
    /// Access the expression whose output is dispatched on in the match statement.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the arms in variant order (declaration order).
    pub fn arms(&self) -> &[EnumMatchArm] {
        &self.arms
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumMatch; scrutinee, arms);

/// Arm of an [`EnumMatch`] expression, ordered by variant.
#[derive(Clone, Debug)]
pub struct EnumMatchArm {
    /// Pattern binding the variant's payload. [`Pattern::Ignore`] for unit
    /// variants.
    pattern: Pattern,
    body: Arc<Expression>,
    span: Span,
}

impl EnumMatchArm {
    /// Access the pattern that binds the variant's payload.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Access the expression that is executed in the match arm.
    pub fn body(&self) -> &Expression {
        &self.body
    }

    /// Access the span of the complete enum match arm.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumMatchArm; pattern, body);

/// Construction of an enum variant: the variant's position and its payload
/// expressions. The enum's definition lives in the type of the enclosing
/// [`SingleExpression`].
#[derive(Clone, Debug)]
pub struct EnumConstruction {
    variant_index: usize,
    payload: Arc<[Arc<Expression>]>,
    span: Span,
}

impl EnumConstruction {
    /// Access the constructed variant's position among the declared variants.
    pub fn variant_index(&self) -> usize {
        self.variant_index
    }

    /// Access the payload expressions. Empty for unit variants.
    pub fn payload(&self) -> &[Arc<Expression>] {
        &self.payload
    }
}

impl_eq_hash!(EnumConstruction; variant_index, payload);

impl AsRef<Span> for EnumConstruction {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for EnumMatch {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// Arm of a [`Match`] expression.
#[derive(Clone, Debug)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
    span: Span,
}

impl MatchArm {
    /// Access the pattern of the match arm.
    pub fn pattern(&self) -> &MatchPattern {
        &self.pattern
    }

    /// Access the expression of the match arm.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the span of the complete match arm.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(MatchArm; pattern, expression);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ExprTree<'a> {
    Expression(&'a Expression),
    Block(&'a [Statement], &'a Option<Arc<Expression>>),
    Statement(&'a Statement),
    Assignment(&'a Assignment),
    Single(&'a SingleExpression),
    Call(&'a Call),
    Match(&'a Match),
    EnumMatch(&'a EnumMatch),
}

impl TreeLike for ExprTree<'_> {
    fn as_node(&self) -> Tree<Self> {
        use SingleExpressionInner as S;

        match self {
            Self::Expression(expr) => match expr.inner() {
                ExpressionInner::Block(statements, maybe_expr) => {
                    Tree::Unary(Self::Block(statements, maybe_expr))
                }
                ExpressionInner::Single(single) => Tree::Unary(Self::Single(single)),
            },
            Self::Block(statements, maybe_expr) => Tree::Nary(
                statements
                    .iter()
                    .map(Self::Statement)
                    .chain(maybe_expr.iter().map(Arc::as_ref).map(Self::Expression))
                    .collect(),
            ),
            Self::Statement(statement) => match statement {
                Statement::Assignment(assignment) => Tree::Unary(Self::Assignment(assignment)),
                Statement::Expression(expression) => Tree::Unary(Self::Expression(expression)),
            },
            Self::Assignment(assignment) => Tree::Unary(Self::Expression(assignment.expression())),
            Self::Single(single) => match single.inner() {
                S::Constant(_)
                | S::Witness(_)
                | S::Parameter(_)
                | S::Variable(_)
                | S::Option(None) => Tree::Nullary,
                S::Expression(l)
                | S::Either(Either::Left(l))
                | S::Either(Either::Right(l))
                | S::Option(Some(l)) => Tree::Unary(Self::Expression(l)),
                S::Tuple(elements) | S::Array(elements) | S::List(elements) => {
                    Tree::Nary(elements.iter().map(Self::Expression).collect())
                }
                S::Call(call) => Tree::Unary(Self::Call(call)),
                S::Match(match_) => Tree::Unary(Self::Match(match_)),
                S::EnumMatch(enum_match) => Tree::Unary(Self::EnumMatch(enum_match)),
                S::EnumConstruction(construction) => Tree::Nary(
                    construction
                        .payload()
                        .iter()
                        .map(|arg| Self::Expression(arg))
                        .collect(),
                ),
            },
            Self::Call(call) => Tree::Nary(call.args().iter().map(Self::Expression).collect()),
            Self::Match(match_) => Tree::Nary(Arc::new([
                Self::Expression(match_.scrutinee()),
                Self::Expression(match_.left().expression()),
                Self::Expression(match_.right().expression()),
            ])),
            Self::EnumMatch(enum_match) => Tree::Nary(
                std::iter::once(Self::Expression(enum_match.scrutinee()))
                    .chain(
                        enum_match
                            .arms()
                            .iter()
                            .map(|arm| Self::Expression(arm.body())),
                    )
                    .collect(),
            ),
        }
    }
}

impl AsRef<Span> for Assignment {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for FunctionParam {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for CustomFunction {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Expression {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for SingleExpression {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Call {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Match {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for MatchArm {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for EnumMatchArm {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

#[cfg(test)]
mod multi_error_tests {
    use crate::test_utils::assert_errors;

    #[test]
    fn tuple_elements() {
        assert_errors(
            "fn main() { let pair: (u32, u32) = (x, y); }",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn array_length_and_elements() {
        assert_errors(
            "fn main() { let array: [u32; 3] = [x, y]; }",
            &[
                "Expected expression of type `[u32; 3]`; found something else",
                "Variable `x` is not defined",
                "Variable `y` is not defined",
            ],
        );
    }

    #[test]
    fn call_output_type_and_arguments() {
        assert_errors(
            "fn main() { let sum: bool = jet::add_32(a, b); }",
            &[
                "Expected expression of type `bool`, found type `(bool, u32)`",
                "Variable `a` is not defined",
                "Variable `b` is not defined",
            ],
        );
    }

    #[test]
    fn nested_errors_are_reported_once() {
        assert_errors(
            "fn main() { let pair: (u32, u32) = (jet::add_32(a, 1), b); }",
            &[
                "Expected expression of type `u32`, found type `(bool, u32)`",
                "Variable `a` is not defined",
                "Variable `b` is not defined",
            ],
        );
    }

    #[test]
    fn match_arms() {
        assert_errors(
            "fn main() {
                let input: Either<u32, u32> = Left(1);
                let result: u32 = match input {
                    Left(l: u32) => left_var,
                    Right(r: u32) => right_var,
                };
            }",
            &[
                "Variable `left_var` is not defined",
                "Variable `right_var` is not defined",
            ],
        );
    }

    #[test]
    fn enum_match_misspelled_variants_are_not_reported_as_missing() {
        assert_errors(
            "enum Color { Red, Green, Blue }
            fn main() {
                let c: Color = Color::Red;
                match c {
                    Color::Rd => {},
                    Color::Gren => {},
                    Color::Blue => {},
                }
            }",
            &[
                "Grammar error: variant 'Rd' is not defined in enum 'Color'",
                "Grammar error: variant 'Gren' is not defined in enum 'Color'",
            ],
        );
    }

    #[test]
    fn enum_match_arms() {
        assert_errors(
            "enum Color { Red, Green }
            fn main() {
                let c: Color = Color::Red;
                let n: u32 = match c {
                    Color::Red => x,
                    Color::Green => y,
                };
            }",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn main_visibility_and_inputs() {
        // The body is not analyzed: it could use the parameters,
        // which would only repeat the error about inputs.
        assert_errors(
            "pub fn main(a: u32) -> u32 { undefined }",
            &[
                "Main function cannot be public",
                "Main function takes no input parameters",
            ],
        );
    }

    #[test]
    fn main_visibility_and_body() {
        assert_errors(
            "pub fn main() { let a: u32 = undefined; }",
            &[
                "Main function cannot be public",
                "Variable `undefined` is not defined",
            ],
        );
    }

    #[test]
    fn enum_duplicate_variants() {
        assert_errors(
            "enum Color { Red, Red, Green, Green }
            fn main() {}",
            &[
                "Grammar error: enum 'Color' has duplicate variant name 'Red'",
                "Grammar error: enum 'Color' has duplicate variant name 'Green'",
            ],
        );
    }

    #[test]
    fn enum_payload_types() {
        assert_errors(
            "enum Shape { Circle(Radius), Square(Side) }
            fn main() {}",
            &[
                "Type alias `Radius` is not defined",
                "Type alias `Side` is not defined",
            ],
        );
    }

    #[test]
    fn failed_check_does_not_stop_the_next_statement() {
        assert_errors(
            "fn main() {
                let b: bool = jet::add_32(1, 2);
                let c: u32 = z;
            }",
            &[
                "Expected expression of type `bool`, found type `(bool, u32)`",
                "Variable `z` is not defined",
            ],
        );
    }

    #[test]
    fn every_broken_function_is_reported() {
        assert_errors(
            "fn a() -> u32 { x }
            fn b() -> u32 { y }
            fn main() {}",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn wrong_call_of_function_with_broken_body_is_reported() {
        assert_errors(
            "fn f(a: u32) -> u32 { x }
            fn main() { let y: bool = f(true); }",
            &[
                "Variable `x` is not defined",
                "Expected expression of type `bool`, found type `u32`",
                "Expected expression of type `u32`, found type `bool`",
            ],
        );
    }

    #[test]
    fn function_with_broken_body_can_still_be_folded() {
        assert_errors(
            "fn add(element: u32, acc: u32) -> u32 { x }
            fn main() {
                let array: [u32; 3] = [1, 2, 3];
                let sum: u32 = array_fold::<add, 3>(array, 0);
            }",
            &["Variable `x` is not defined"],
        );
    }

    #[test]
    fn function_with_broken_body_can_still_be_imported() {
        assert_errors(
            "mod m { pub fn f() -> u32 { x } }
            use crate::m::f;
            fn main() { let y: u32 = f(); }",
            &["Variable `x` is not defined"],
        );
    }

    #[test]
    fn broken_function_in_module_does_not_stop_the_next_item() {
        assert_errors(
            "mod m { fn f() -> u32 { x } }
            fn g() -> u32 { y }
            fn main() {}",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn broken_main_does_not_stop_the_next_item() {
        assert_errors(
            "fn main() { let a: u32 = x; }
            fn g() -> u32 { y }",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn missing_main_is_reported_with_other_errors() {
        assert_errors(
            "fn f() -> u32 { x }",
            &["Main function is required", "Variable `x` is not defined"],
        );
    }

    #[test]
    fn broken_main_in_module_does_not_stop_the_next_item() {
        assert_errors(
            "mod entry { fn main() { let x: u32 = missing; } }
            fn later() -> u32 { later_missing }",
            &[
                "Variable `missing` is not defined",
                "Variable `later_missing` is not defined",
            ],
        );
    }

    #[test]
    fn broken_main_in_nested_module_does_not_stop_the_next_item() {
        assert_errors(
            "mod outer {
                mod inner { fn main() { let x: u32 = missing; } }
                fn sibling() -> u32 { sibling_missing }
            }
            fn later() -> u32 { later_missing }",
            &[
                "Variable `missing` is not defined",
                "Variable `sibling_missing` is not defined",
                "Variable `later_missing` is not defined",
            ],
        );
    }

    #[test]
    fn undefined_types_are_reported_once() {
        assert_errors(
            "type Alias = Missing;
            fn f(a: Alias) -> Alias { a }
            fn g(a: Undefined) -> Unknown { a }
            fn h() -> u32 { y }

            fn main() { let x: u32 = f(1); }",
            &[
                "Type alias `Missing` is not defined",
                "Type alias `Undefined` is not defined",
                "Type alias `Unknown` is not defined",
                "Variable `y` is not defined",
            ],
        );
    }

    #[test]
    fn broken_parameter_does_not_hide_other_errors() {
        assert_errors(
            "fn f(a: Missing, b: u32) -> u32 { b }
            fn main() {
                let t: bool = true;
                let y: u32 = f((1, x), t);
            }",
            &[
                "Type alias `Missing` is not defined",
                "Variable `x` is not defined",
                "Expected expression of type `u32`, found type `bool`",
            ],
        );
    }

    #[test]
    fn broken_enum_payload_does_not_hide_the_enum() {
        assert_errors(
            "enum E { A(Missing), B }
            fn main() {
                let e: E = E::B;
                let n: u32 = match e {
                    E::A(a: u32) => a,
                    E::B => x,
                };
            }",
            &[
                "Type alias `Missing` is not defined",
                "Variable `x` is not defined",
            ],
        );
    }

    #[test]
    fn parameter_ignores_uses_of_broken_types() {
        assert_errors(
            "type Alias = Missing;
            fn main() {
                let a: Alias = param::X;
                let b: u32 = param::X;
                let c: bool = param::X;
            }",
            &[
                "Type alias `Missing` is not defined",
                "Expected expression of type `u32`, found type `bool`",
            ],
        );
    }

    #[test]
    fn cast_of_enum_with_broken_payload() {
        assert_errors(
            "enum E { A(Missing), B }
            enum F { A(u8), B }
            fn different(e: E) -> F { <E>::into(e) }
            fn same(e: E) -> Option<E> { <Option<E>>::into(Some(e)) }

            fn main() {}",
            &[
                "Type alias `Missing` is not defined",
                "Cannot cast values of type `E` as values of type `F`",
            ],
        );
    }

    #[test]
    fn constant_of_broken_type_is_rejected() {
        use crate::parse::{self, ParseFromStr};
        use crate::types::{ResolvedType, TypeConstructible};

        let never = ResolvedType::never();
        let option_never = ResolvedType::option(never.clone());

        for (source, ty) in [
            ("5", never),
            ("5", option_never.clone()),
            ("[None, None]", ResolvedType::array(option_never, 3)),
        ] {
            let parsed = parse::Expression::parse_from_str(source).expect("value parses");
            assert!(super::Expression::analyze_const(&parsed, &ty).is_err());
        }
    }

    #[test]
    fn construction_through_broken_enum_alias() {
        assert_errors(
            "type Bad = Missing;
            enum Color { Red, Green }

            fn unknown_variant() -> Color { Bad::Blue }
            fn payload_count() -> Color { Bad::Red(x) }
            fn mixed_arms(c: Color) {
                match c {
                    Color::Red => {},
                    Bad::Green => {}
                }
            }

            fn main() {}",
            &[
                "Type alias `Missing` is not defined",
                "Variable `x` is not defined",
                "Grammar error: all match arms must use the same enum; expected 'Color', found 'Bad'",
            ],
        );
    }

    #[test]
    fn errors_mentioning_broken_types_are_not_reported() {
        assert_errors(
            "type Alias = Missing;
            fn f(a: (Alias, u32)) {}
            fn g() { f(1) }
            fn main() { let x: Option<Alias> = 5; }",
            &["Type alias `Missing` is not defined"],
        );
    }

    /// Aliases like `type A1 = (A0, A0);` up to `A{depth}`, whose resolved types share their parts.
    fn shared_aliases(name: &str, leaf: &str, depth: usize) -> String {
        let mut source = format!("type {name}0 = {leaf};\n");
        for i in 1..=depth {
            source += &format!("type {name}{i} = ({name}{0}, {name}{0});\n", i - 1);
        }
        source
    }

    #[test]
    fn shared_types_are_fast() {
        let source = shared_aliases("A", "u8", 64)
            + &shared_aliases("B", "Missing", 64)
            + &shared_aliases("C", "u8", 64)
            + "enum E { V(Unknown) }\n"
            + &shared_aliases("G", "E", 64)
            + &shared_aliases("H", "E", 64)
            + "fn cast(a: A64) -> B64 { <A64>::into(a) }
            fn enum_cast(g: G64) -> H64 { <G64>::into(g) }

            fn main() {
                let b: B64 = param::X;
                let a: A64 = param::X;
                let c: C64 = param::X;
            }";

        assert_errors(
            &source,
            &[
                "Type alias `Missing` is not defined",
                "Type alias `Unknown` is not defined",
            ],
        );
    }

    #[test]
    fn builtins_accept_broken_types() {
        assert_errors(
            "type Alias = Missing;
            fn cast() -> u32 { <Alias>::into(x) }
            fn add(element: Alias, acc: u32) -> u32 { acc }
            fn fold(array: [Alias; 2]) -> u32 { array_fold::<add, 2>(array, 0) }
            fn step(acc: u32, context: (), counter: Alias) -> Either<u32, u32> { Right(acc) }
            fn looped() -> Either<u32, u32> { for_while::<step>(0, ()) }
            fn hash(tuple: (Alias,)) -> u256 { raw_hash::<(Alias,)>(tuple) }

            fn main() { let z: u32 = y; }",
            &[
                "Type alias `Missing` is not defined",
                "Variable `x` is not defined",
                "Variable `y` is not defined",
            ],
        );
    }
}

#[cfg(test)]
mod scope_resolution_tests {
    use crate::ast::tests::{analyze, analyze_multifile};

    #[test]
    fn duplicate_function_parameter_is_rejected() {
        let err = analyze(
            "fn f(a: u256, a: Pubkey) -> u256 { a }
            fn main() {
                let _: u256 = f(0, 1);
            }",
        )
        .unwrap_err();

        assert!(
            err.contains("Parameter `a` was defined multiple times"),
            "{err}"
        );
    }

    #[test]
    fn private_type_alias_from_dependency_does_not_leak() {
        let result = analyze_multifile(vec![
            (
                "main.simf",
                "use lib::A::helper; fn main() { helper(); let x: Secret = 0; }",
            ),
            ("libs/lib/A.simf", "type Secret = u32; pub fn helper() {}"),
        ]);

        assert!(
            result.is_err(),
            "private alias from another file leaked into root scope: {result:?}"
        );
    }

    #[test]
    fn same_alias_name_in_different_modules_does_not_conflict_if_only_one_is_imported() {
        let result = analyze_multifile(vec![
            (
                "main.simf",
                "use lib::A::Word; use lib::B::id; fn main() { let x: Word = 0; assert!(jet::is_zero_32(id(x))); }",
            ),
            ("libs/lib/A.simf", "pub type Word = u32;"),
            ("libs/lib/B.simf", "pub type Word = u16; pub fn id(x: u32) -> u32 { x }"),
        ]);

        assert!(
            result.is_ok(),
            "unimported alias from another module should not collide: {result:?}"
        );
    }

    #[test]
    fn main_must_be_defined_once_per_project() {
        let result = analyze_multifile(vec![
            ("main.simf", "use lib::A::helper; fn main() { helper(); }"),
            ("libs/lib/A.simf", "fn main() {} pub fn helper() {}"),
        ]);

        assert!(
            result.is_err(),
            "Main function must be inside an entry file: {result:?}"
        );
    }

    #[test]
    fn test_local_definitions_visibility() {
        // main.simf defines a private function and a public function.
        // Expected: Both should be usable locally in main.
        let result = analyze_multifile(vec![(
            "main.simf",
            "fn private_fn() {} pub fn public_fn() {} fn main() { private_fn(); public_fn(); }",
        )]);

        assert!(
            result.is_ok(),
            "Local definitions should be visible: {result:?}"
        );
    }

    #[test]
    fn test_pub_use_propagation() {
        // Scenario: Re-exporting.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub use crate::A::foo;"),
            ("main.simf", "use lib::B::foo; fn main() { foo(); }"),
        ]);

        assert!(
            result.is_ok(),
            "Public re-exports must be visible: {result:?}"
        );
    }

    #[test]
    fn test_private_import_encapsulation_error() {
        // Scenario: A private import cannot be re-exported.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "use crate::A::foo;"), // <--- Private binding!
            ("main.simf", "use lib::B::foo; fn main() {}"),
        ]);

        let err = result.expect_err("Private imports should not be accessible");
        assert!(err.contains("private") || err.contains("foo"));
    }

    #[test]
    fn test_separated_type_aliases_and_functions() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32; pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::bar; fn main() { bar(); let x: bar = 0; }",
            ),
        ]);

        assert!(
            result.is_ok(),
            "AST should support separate namespaces for types and functions: {result:?}"
        );
    }

    #[test]
    fn test_public_main_is_forbidden() {
        let result = analyze_multifile(vec![("main.simf", "pub fn main() {}")]);

        let err = result.expect_err("Public main should be rejected");
        assert!(err.contains("Main") && err.contains("public"));
    }

    #[test]
    fn test_aliasing_to_main_is_forbidden() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32;"),
            ("main.simf", "use lib::A::bar as main; fn main() {}"),
        ]);

        let err = result.expect_err("Aliasing to main should be rejected");
        assert!(err.contains("Main") && err.contains("alias"));
    }

    #[test]
    fn test_renaming_with_use() {
        // Expected: "bar" is usable, "foo" is not.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            (
                "main.simf",
                "use lib::A::foo as bar; fn main() { bar(); foo(); }",
            ),
        ]);

        let err = result.expect_err("Using the original unaliased name 'foo' should fail");
        assert!(err.contains("foo") && (err.contains("not defined") || err.contains("unresolved")));
    }

    #[test]
    fn test_multiple_aliases_in_list() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {} pub fn baz() {}"),
            (
                "main.simf",
                "use lib::A::{foo as bar, baz as qux}; fn main() { bar(); qux(); }",
            ),
        ]);

        assert!(
            result.is_ok(),
            "List aliases should be resolvable: {result:?}"
        );
    }

    #[test]
    fn test_alias_private_item_fails() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "fn secret() {}"),
            ("main.simf", "use lib::A::secret as my_secret; fn main() {}"),
        ]);

        let err = result.expect_err("Aliasing a private item should fail");
        assert!(err.contains("secret") && err.contains("private"));
    }

    #[test]
    fn test_deep_reexport_with_aliases() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn original() {}"),
            ("libs/lib/B.simf", "pub use crate::A::original as middle;"),
            (
                "main.simf",
                "use lib::B::middle as final_name; fn main() { final_name(); }",
            ),
        ]);

        assert!(
            result.is_ok(),
            "Deep alias re-exports should work: {result:?}"
        );
    }

    #[test]
    fn test_deep_reexport_private_link_fails() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn target() {}"),
            ("libs/lib/B.simf", "use crate::A::target as hidden_alias;"),
            ("main.simf", "use lib::B::hidden_alias; fn main() {}"),
        ]);

        let err = result.expect_err("Private intermediate aliases should block resolution");
        assert!(err.contains("hidden_alias") && err.contains("private"));
    }

    #[test]
    fn test_plain_import_and_alias_to_same_name_is_rejected() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub fn foo() {}"),
            (
                "main.simf",
                "use lib::A::foo; use lib::B::foo as foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Duplicate names in scope should fail");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    fn test_alias_cannot_reuse_local_definition_name() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "pub fn foo() {} use lib::A::bar as foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Alias reusing a local name should fail");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    #[ignore = "Pending better error handler:private item errors currently mask duplicate imports"]
    fn test_private_alias_error_does_not_mask_duplicate_function_import() {
        // Scenario: Loading a private item fails, but we must STILL catch if a
        // secondary import tries to bind to the same name.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub fn foo() {} type foo = u32;"),
            (
                "main.simf",
                "use lib::A::foo; use lib::B::foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Duplicate function import should fail");

        // It shouldn't just complain about the private type `foo`; it must also
        // complain that `foo` was imported twice!
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    fn test_failed_alias_import_does_not_poison_following_imports() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn nope() {}"),
            ("libs/lib/B.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::missing as foo; use lib::B::bar as foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Build should fail on the unresolved import");

        // It should complain about `missing`, but NOT about `foo` being duplicated,
        // because the first import failed and never actually reserved the name `foo`.
        assert!(err.contains("missing") || err.contains("not found"));
        assert!(!err.contains("multiple times"));
    }

    #[test]
    fn test_local_function_cannot_reuse_alias_name() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::bar as foo; pub fn foo() {} fn main() {}",
            ),
        ]);

        let err =
            result.expect_err("Build should fail when a local definition reuses an alias name");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    fn test_local_type_alias_cannot_reuse_alias_name() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32;"),
            (
                "main.simf",
                "use lib::A::bar as foo; type foo = u64; fn main() {}",
            ),
        ]);

        let err =
            result.expect_err("Build should fail when a local definition reuses an alias name");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }
}
