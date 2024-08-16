use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;

use either::Either;
use simplicity::jet::Elements;

use crate::error::{Error, RichError, Span, WithSpan};
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::parse;
use crate::parse::MatchPattern;
use crate::pattern::Pattern;
use crate::str::{FunctionName, Identifier, WitnessName};
use crate::types::{
    AliasedType, ResolvedType, StructuralType, TypeConstructible, TypeDeconstructible, UIntType,
};
use crate::value::{UIntValue, Value};

/// Map of witness names to their expected type, as declared in the program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclaredWitnesses(HashMap<WitnessName, ResolvedType>);

impl DeclaredWitnesses {
    /// Get the expected type of the given witness `name`.
    pub fn get(&self, name: &WitnessName) -> Option<&ResolvedType> {
        self.0.get(name)
    }
}

/// A program consists of the main function.
///
/// Other items such as custom functions or type aliases
/// are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    main: Expression,
    witnesses: DeclaredWitnesses,
}

impl Program {
    /// Access the main function.
    ///
    /// There is exactly one main function for each program.
    pub fn main(&self) -> &Expression {
        &self.main
    }

    /// Access the map of declared witnesses.
    pub fn witnesses(&self) -> &DeclaredWitnesses {
        &self.witnesses
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
    /// A function.
    Function(Function),
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
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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
}

/// An expression returns a value.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Expression {
    inner: ExpressionInner,
    ty: ResolvedType,
    span: Span,
}

impl Expression {
    /// Access the inner expression.
    pub fn inner(&self) -> &ExpressionInner {
        &self.inner
    }

    /// Access the type of the expression.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
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
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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
}

/// Variant of a single expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SingleExpressionInner {
    /// Constant value.
    Constant(Value),
    /// Witness value.
    Witness(WitnessName),
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
}

/// Call of a user-defined or of a builtin function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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
}

/// Name of a called function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CallName {
    /// Elements jet.
    Jet(Elements),
    /// [`Either::unwrap_left`].
    UnwrapLeft(ResolvedType),
    /// [`Either::unwrap_right`].
    UnwrapRight(ResolvedType),
    /// [`Option::is_none`].
    IsNone(ResolvedType),
    /// [`Option::unwrap`].
    Unwrap,
    /// [`assert`].
    Assert,
    /// [`panic`] without error message.
    Panic,
    /// Cast from the given source type.
    TypeCast(ResolvedType),
    /// A custom function that was defined previously.
    ///
    /// We effectively copy the function body into every call of the function.
    /// We use [`Arc`] for cheap clones during this process.
    Custom(CustomFunction),
    /// Fold of a bounded list with the given function.
    Fold(CustomFunction, NonZeroPow2Usize),
    /// Loop over the given function a bounded number of times until it returns success.
    ForWhile(CustomFunction, Pow2Usize),
}

/// Definition of a custom function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct CustomFunction {
    params: Arc<[FunctionParam]>,
    body: Arc<Expression>,
}

impl CustomFunction {
    /// Access the identifiers of the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the body of the function.
    pub fn body(&self) -> &Expression {
        &self.body
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

/// Parameter of a function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionParam {
    identifier: Identifier,
    ty: ResolvedType,
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
}

/// Match expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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
}

/// Arm of a [`Match`] expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
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
}

/// Scope for generating the abstract syntax tree.
///
/// The scope is used for:
/// 1. Assigning types to each variable
/// 2. Resolving type aliases
/// 3. Assigning types to each witness expression
/// 4. Resolving calls to custom functions
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct Scope {
    variables: Vec<HashMap<Identifier, ResolvedType>>,
    aliases: HashMap<Identifier, ResolvedType>,
    witnesses: HashMap<WitnessName, ResolvedType>,
    functions: HashMap<FunctionName, CustomFunction>,
    is_main: bool,
}

impl Scope {
    /// Check if the current scope is topmost.
    pub fn is_topmost(&self) -> bool {
        self.variables.is_empty()
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
    }

    /// Push the scope of the main function onto the stack.
    ///
    /// ## Panics
    ///
    /// - The current scope is already inside the main function.
    /// - The current scope is not topmost.
    pub fn push_main_scope(&mut self) {
        assert!(!self.is_main, "Already inside main function");
        assert!(self.is_topmost(), "Current scope is not topmost");
        self.push_scope();
        self.is_main = true;
    }

    /// Pop the current scope from the stack.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Stack is empty");
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// ## Panics
    ///
    /// - The current scope is not inside the main function.
    /// - The current scope is not nested in the topmost scope.
    pub fn pop_main_scope(&mut self) {
        assert!(self.is_main, "Current scope is not inside main function");
        self.pop_scope();
        self.is_main = false;
        assert!(
            self.is_topmost(),
            "Current scope is not nested in topmost scope"
        )
    }

    /// Push a variable onto the current stack.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert_variable(&mut self, identifier: Identifier, ty: ResolvedType) {
        self.variables
            .last_mut()
            .expect("Stack is empty")
            .insert(identifier, ty);
    }

    /// Get the type of the variable.
    pub fn get_variable(&self, identifier: &Identifier) -> Option<&ResolvedType> {
        self.variables
            .iter()
            .rev()
            .find_map(|scope| scope.get(identifier))
    }

    /// Resolve a type with aliases to a type without aliases.
    ///
    /// ## Errors
    ///
    /// There are any undefined aliases.
    pub fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Error> {
        let get_alias =
            |name: &Identifier| -> Option<ResolvedType> { self.aliases.get(name).cloned() };
        ty.resolve(get_alias).map_err(Error::UndefinedAlias)
    }

    /// Push a type alias into the global map.
    ///
    /// ## Errors
    ///
    /// There are any undefined aliases.
    pub fn insert_alias(&mut self, alias: Identifier, ty: AliasedType) -> Result<(), Error> {
        let resolved_ty = self.resolve(&ty)?;
        self.aliases.insert(alias, resolved_ty);
        Ok(())
    }

    /// Insert a witness into the global map.
    ///
    /// ## Errors
    ///
    /// - The current scope is not inside the main function.
    /// - The witness name has already been defined somewhere else in the program.
    pub fn insert_witness(&mut self, name: WitnessName, ty: ResolvedType) -> Result<(), Error> {
        if !self.is_main {
            return Err(Error::WitnessOutsideMain);
        }

        match self.witnesses.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::WitnessReused(name)),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Consume the scope and return the map of witness names to their expected type.
    ///
    /// Use this map to finalize the Simfony program with witness values of the same type.
    pub fn into_witnesses(self) -> HashMap<WitnessName, ResolvedType> {
        self.witnesses
    }

    /// Insert a custom function into the global map.
    ///
    /// ## Errors
    ///
    /// The function has already been defined.
    pub fn insert_function(
        &mut self,
        name: FunctionName,
        function: CustomFunction,
    ) -> Result<(), Error> {
        match self.functions.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::FunctionRedefined(name)),
            Entry::Vacant(entry) => {
                entry.insert(function);
                Ok(())
            }
        }
    }

    /// Get the definition of a custom function.
    pub fn get_function(&self, name: &FunctionName) -> Option<&CustomFunction> {
        self.functions.get(name)
    }
}

/// Part of the abstract syntax tree that can be generated from a precursor in the parse tree.
trait AbstractSyntaxTree: Sized {
    /// Component of the parse tree.
    type From;

    /// Analyze a component from the parse tree
    /// and convert it into a component of the abstract syntax tree.
    ///
    /// Check if the analyzed expression is of the expected type.
    /// Statements return no values so their expected type is always unit.
    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError>;
}

impl Program {
    pub fn analyze(from: &parse::Program) -> Result<Self, RichError> {
        let unit = ResolvedType::unit();
        let mut scope = Scope::default();
        let items = from
            .items()
            .iter()
            .map(|s| Item::analyze(s, &unit, &mut scope))
            .collect::<Result<Vec<Item>, RichError>>()?;
        debug_assert!(scope.is_topmost());
        let witnesses = DeclaredWitnesses(scope.into_witnesses());

        let mut mains = items
            .into_iter()
            .filter_map(|item| match item {
                Item::Function(Function::Main(expr)) => Some(expr),
                _ => None,
            })
            .collect::<Vec<Expression>>();
        let main = match mains.len() {
            0 => return Err(Error::MainRequired).with_span(from),
            1 => mains.pop().unwrap(),
            _ => {
                return Err(Error::FunctionRedefined(FunctionName::main()))
                    .with_span(mains.first().unwrap())
            }
        };

        Ok(Self { main, witnesses })
    }
}

impl AbstractSyntaxTree for Item {
    type From = parse::Item;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        assert!(ty.is_unit(), "Items cannot return anything");
        assert!(scope.is_topmost(), "Items live in the topmost scope only");

        match from {
            parse::Item::TypeAlias(alias) => {
                scope
                    .insert_alias(alias.name.clone(), alias.ty.clone())
                    .with_span(alias)?;
                Ok(Self::TypeAlias)
            }
            parse::Item::Function(function) => {
                Function::analyze(function, ty, scope).map(Self::Function)
            }
        }
    }
}

impl AbstractSyntaxTree for Function {
    type From = parse::Function;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        assert!(ty.is_unit(), "Function definitions cannot return anything");
        assert!(scope.is_topmost(), "Items live in the topmost scope only");

        if from.name().as_inner() != "main" {
            let params = from
                .params()
                .iter()
                .map(|param| {
                    let identifier = param.identifier().clone();
                    let ty = scope.resolve(param.ty())?;
                    Ok(FunctionParam { identifier, ty })
                })
                .collect::<Result<Arc<[FunctionParam]>, Error>>()
                .with_span(from)?;
            let ret = from
                .ret()
                .as_ref()
                .map(|aliased| scope.resolve(aliased).with_span(from))
                .transpose()?
                .unwrap_or_else(ResolvedType::unit);
            scope.push_scope();
            for param in params.iter() {
                scope.insert_variable(param.identifier().clone(), param.ty().clone());
            }
            let body = Expression::analyze(from.body(), &ret, scope).map(Arc::new)?;
            scope.pop_scope();
            debug_assert!(scope.is_topmost());
            let function = CustomFunction { params, body };
            scope
                .insert_function(from.name().clone(), function)
                .with_span(from)?;

            return Ok(Self::Custom);
        }

        if !from.params().is_empty() {
            return Err(Error::MainNoInputs).with_span(from);
        }
        if let Some(aliased) = from.ret() {
            let resolved = scope.resolve(aliased).with_span(from)?;
            if !resolved.is_unit() {
                return Err(Error::MainNoOutput).with_span(from);
            }
        }

        scope.push_main_scope();
        let body = Expression::analyze(from.body(), ty, scope)?;
        scope.pop_main_scope();
        Ok(Self::Main(body))
    }
}

impl AbstractSyntaxTree for Statement {
    type From = parse::Statement;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        assert!(ty.is_unit(), "Statements cannot return anything");
        match from {
            parse::Statement::Assignment(assignment) => {
                Assignment::analyze(assignment, ty, scope).map(Self::Assignment)
            }
            parse::Statement::Expression(expression) => {
                Expression::analyze(expression, ty, scope).map(Self::Expression)
            }
        }
    }
}

impl AbstractSyntaxTree for Assignment {
    type From = parse::Assignment;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        assert!(ty.is_unit(), "Assignments cannot return anything");
        // The assignment is a statement that returns nothing.
        //
        // However, the expression evaluated in the assignment does have a type,
        // namely the type specified in the assignment.
        let ty_expr = scope.resolve(&from.ty).with_span(from)?;
        let expression = Expression::analyze(&from.expression, &ty_expr, scope)?;
        let typed_variables = from.pattern.is_of_type(&ty_expr).with_span(from)?;
        for (identifier, ty) in typed_variables {
            scope.insert_variable(identifier, ty);
        }

        Ok(Self {
            pattern: from.pattern.clone(),
            expression,
            span: from.span,
        })
    }
}

impl AbstractSyntaxTree for Expression {
    type From = parse::Expression;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        match &from.inner {
            parse::ExpressionInner::Single(single) => {
                let ast_single = SingleExpression::analyze(single, ty, scope)?;
                Ok(Self {
                    ty: ty.clone(),
                    inner: ExpressionInner::Single(ast_single),
                    span: from.span,
                })
            }
            parse::ExpressionInner::Block(statements, expression) => {
                scope.push_scope();
                let ast_statements = statements
                    .iter()
                    .map(|s| Statement::analyze(s, &ResolvedType::unit(), scope))
                    .collect::<Result<Arc<[Statement]>, RichError>>()?;
                let ast_expression = match expression {
                    Some(expression) => Expression::analyze(expression, ty, scope)
                        .map(Arc::new)
                        .map(Some),
                    None if ty.is_unit() => Ok(None),
                    None => Err(Error::ExpressionTypeMismatch(
                        ty.clone(),
                        ResolvedType::unit(),
                    ))
                    .with_span(from),
                }?;
                scope.pop_scope();

                Ok(Self {
                    ty: ty.clone(),
                    inner: ExpressionInner::Block(ast_statements, ast_expression),
                    span: from.span,
                })
            }
        }
    }
}

impl AbstractSyntaxTree for SingleExpression {
    type From = parse::SingleExpression;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        let inner = match &from.inner {
            parse::SingleExpressionInner::Boolean(bit) => {
                if !ty.is_boolean() {
                    return Err(Error::ExpressionTypeMismatch(
                        ty.clone(),
                        ResolvedType::boolean(),
                    ))
                    .with_span(from);
                }
                SingleExpressionInner::Constant(Value::from(*bit))
            }
            parse::SingleExpressionInner::Decimal(decimal) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                UIntValue::parse_decimal(decimal, ty)
                    .with_span(from)
                    .map(Value::from)
                    .map(SingleExpressionInner::Constant)?
            }
            parse::SingleExpressionInner::BitString(bits) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                let value = UIntValue::parse_bits(bits, ty).with_span(from)?;
                SingleExpressionInner::Constant(Value::from(value))
            }
            parse::SingleExpressionInner::ByteString(bytes) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                let value = UIntValue::parse_bytes(bytes, ty).with_span(from)?;
                SingleExpressionInner::Constant(Value::from(value))
            }
            parse::SingleExpressionInner::Witness(name) => {
                scope
                    .insert_witness(name.clone(), ty.clone())
                    .with_span(from)?;
                SingleExpressionInner::Witness(name.clone())
            }
            parse::SingleExpressionInner::Variable(identifier) => {
                let bound_ty = scope
                    .get_variable(identifier)
                    .ok_or(Error::UndefinedVariable(identifier.clone()))
                    .with_span(from)?;
                if ty != bound_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), bound_ty.clone()))
                        .with_span(from);
                }
                scope.insert_variable(identifier.clone(), ty.clone());
                SingleExpressionInner::Variable(identifier.clone())
            }
            parse::SingleExpressionInner::Expression(parse) => {
                Expression::analyze(parse, ty, scope)
                    .map(Arc::new)
                    .map(SingleExpressionInner::Expression)?
            }
            parse::SingleExpressionInner::Tuple(tuple) => {
                let types = ty
                    .as_tuple()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                if tuple.len() != types.len() {
                    return Err(Error::TypeValueMismatch(ty.clone())).with_span(from);
                }
                tuple
                    .iter()
                    .zip(types.iter())
                    .map(|(el_parse, el_ty)| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()
                    .map(SingleExpressionInner::Tuple)?
            }
            parse::SingleExpressionInner::Array(array) => {
                let (el_ty, size) = ty
                    .as_array()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                if array.len() != size {
                    return Err(Error::TypeValueMismatch(ty.clone())).with_span(from);
                }
                array
                    .iter()
                    .map(|el_parse| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()
                    .map(SingleExpressionInner::Array)?
            }
            parse::SingleExpressionInner::List(list) => {
                let (el_ty, bound) = ty
                    .as_list()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                if bound.get() <= list.len() {
                    return Err(Error::TypeValueMismatch(ty.clone())).with_span(from);
                }
                list.iter()
                    .map(|e| Expression::analyze(e, el_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()
                    .map(SingleExpressionInner::List)?
            }
            parse::SingleExpressionInner::Either(either) => {
                let (ty_l, ty_r) = ty
                    .as_either()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                match either {
                    Either::Left(parse_l) => Expression::analyze(parse_l, ty_l, scope)
                        .map(Arc::new)
                        .map(Either::Left),
                    Either::Right(parse_r) => Expression::analyze(parse_r, ty_r, scope)
                        .map(Arc::new)
                        .map(Either::Right),
                }
                .map(SingleExpressionInner::Either)?
            }
            parse::SingleExpressionInner::Option(maybe_parse) => {
                let ty = ty
                    .as_option()
                    .ok_or(Error::TypeValueMismatch(ty.clone()))
                    .with_span(from)?;
                match maybe_parse {
                    Some(parse) => {
                        Some(Expression::analyze(parse, ty, scope).map(Arc::new)).transpose()
                    }
                    None => Ok(None),
                }
                .map(SingleExpressionInner::Option)?
            }
            parse::SingleExpressionInner::Call(call) => {
                Call::analyze(call, ty, scope).map(SingleExpressionInner::Call)?
            }
            parse::SingleExpressionInner::Match(match_) => {
                Match::analyze(match_, ty, scope).map(SingleExpressionInner::Match)?
            }
        };

        Ok(Self {
            inner,
            ty: ty.clone(),
            span: from.span,
        })
    }
}

impl AbstractSyntaxTree for Call {
    type From = parse::Call;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        let name = CallName::analyze(from, ty, scope)?;

        let args = match name.clone() {
            CallName::Jet(jet) => {
                let args_ty = crate::jet::source_type(jet)
                    .iter()
                    .map(AliasedType::resolve_builtin)
                    .collect::<Result<Vec<ResolvedType>, Identifier>>()
                    .map_err(Error::UndefinedAlias)
                    .with_span(from)?;
                if from.args.len() != args_ty.len() {
                    return Err(Error::InvalidNumberOfArguments(
                        args_ty.len(),
                        from.args.len(),
                    ))
                    .with_span(from);
                }
                let out_ty = crate::jet::target_type(jet)
                    .resolve_builtin()
                    .map_err(Error::UndefinedAlias)
                    .with_span(from)?;
                if ty != &out_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), out_ty)).with_span(from);
                }
                from.args
                    .iter()
                    .zip(args_ty.iter())
                    .map(|(arg_parse, arg_ty)| Expression::analyze(arg_parse, arg_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()?
            }
            CallName::UnwrapLeft(right_ty) => {
                let args_ty = ResolvedType::either(ty.clone(), right_ty);
                if from.args.len() != 1 {
                    return Err(Error::InvalidNumberOfArguments(1, from.args.len()))
                        .with_span(from);
                }
                Arc::from([Expression::analyze(
                    from.args.first().unwrap(),
                    &args_ty,
                    scope,
                )?])
            }
            CallName::UnwrapRight(left_ty) => {
                let args_ty = ResolvedType::either(left_ty, ty.clone());
                if from.args.len() != 1 {
                    return Err(Error::InvalidNumberOfArguments(1, from.args.len()))
                        .with_span(from);
                }
                Arc::from([Expression::analyze(
                    from.args.first().unwrap(),
                    &args_ty,
                    scope,
                )?])
            }
            CallName::IsNone(some_ty) => {
                if from.args.len() != 1 {
                    return Err(Error::InvalidNumberOfArguments(1, from.args.len()))
                        .with_span(from);
                }
                let out_ty = ResolvedType::boolean();
                if ty != &out_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), out_ty)).with_span(from);
                }
                let arg_ty = ResolvedType::option(some_ty);
                Arc::from([Expression::analyze(
                    from.args.first().unwrap(),
                    &arg_ty,
                    scope,
                )?])
            }
            CallName::Unwrap => {
                let args_ty = ResolvedType::option(ty.clone());
                if from.args.len() != 1 {
                    return Err(Error::InvalidNumberOfArguments(1, from.args.len()))
                        .with_span(from);
                }
                Arc::from([Expression::analyze(
                    from.args.first().unwrap(),
                    &args_ty,
                    scope,
                )?])
            }
            CallName::Assert => {
                if from.args.len() != 1 {
                    return Err(Error::InvalidNumberOfArguments(1, from.args.len()))
                        .with_span(from);
                }
                if !ty.is_unit() {
                    return Err(Error::ExpressionTypeMismatch(
                        ty.clone(),
                        ResolvedType::unit(),
                    ))
                    .with_span(from);
                }
                let arg_type = ResolvedType::boolean();
                Arc::from([Expression::analyze(
                    from.args.first().unwrap(),
                    &arg_type,
                    scope,
                )?])
            }
            CallName::Panic => {
                if from.args.len() != 0 {
                    return Err(Error::InvalidNumberOfArguments(0, from.args.len()))
                        .with_span(from);
                }
                // panic! allows every output type because it will never return anything
                Arc::from([])
            }
            CallName::TypeCast(source) => {
                if from.args.len() != 1 {
                    return Err(Error::InvalidNumberOfArguments(1, from.args.len()))
                        .with_span(from);
                }
                if StructuralType::from(&source) != StructuralType::from(ty) {
                    return Err(Error::InvalidCast(source, ty.clone())).with_span(from);
                }
                Arc::from([Expression::analyze(
                    from.args.first().unwrap(),
                    &source,
                    scope,
                )?])
            }
            CallName::Custom(function) => {
                if from.args.len() != function.params().len() {
                    return Err(Error::InvalidNumberOfArguments(
                        function.params().len(),
                        from.args.len(),
                    ))
                    .with_span(from);
                }
                let out_ty = function.body().ty();
                if ty != out_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), out_ty.clone()))
                        .with_span(from);
                }
                from.args
                    .iter()
                    .zip(function.params.iter().map(FunctionParam::ty))
                    .map(|(arg_parse, arg_ty)| Expression::analyze(arg_parse, arg_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()?
            }
            CallName::Fold(function, bound) => {
                if from.args.len() != 2 {
                    return Err(Error::InvalidNumberOfArguments(2, from.args.len()))
                        .with_span(from);
                }
                let out_ty = function.body().ty();
                if ty != out_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), out_ty.clone()))
                        .with_span(from);
                }
                // A list fold has the signature:
                //   fold::<f, N>(list: List<E, N>, initial_accumulator: A) -> A
                // where
                //   fn f(element: E, accumulator: A) -> A
                let element_ty = function.params().first().expect("foldable function").ty();
                let list_ty = ResolvedType::list(element_ty.clone(), bound);
                let accumulator_ty = function.params().get(1).expect("foldable function").ty();
                from.args
                    .iter()
                    .zip([&list_ty, accumulator_ty])
                    .map(|(arg_parse, arg_ty)| Expression::analyze(arg_parse, arg_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()?
            }
            CallName::ForWhile(function, _bit_width) => {
                if from.args.len() != 2 {
                    return Err(Error::InvalidNumberOfArguments(2, from.args.len()))
                        .with_span(from);
                }
                let out_ty = function.body().ty();
                if ty != out_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), out_ty.clone()))
                        .with_span(from);
                }
                // A for-while loop has the signature:
                //   for_while::<f>(initial_accumulator: A, readonly_context: C) -> Either<B, A>
                // where
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                //   N is a power of two
                let accumulator_ty = function.params().first().expect("loopable function").ty();
                let context_ty = function.params().get(1).expect("loopable function").ty();
                from.args
                    .iter()
                    .zip([accumulator_ty, context_ty])
                    .map(|(arg_parse, arg_ty)| Expression::analyze(arg_parse, arg_ty, scope))
                    .collect::<Result<Arc<[Expression]>, RichError>>()?
            }
        };

        Ok(Self {
            name,
            args,
            span: from.span,
        })
    }
}

impl AbstractSyntaxTree for CallName {
    // Take parse::Call, so we have access to the span for pretty errors
    type From = parse::Call;

    fn analyze(
        from: &Self::From,
        _ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, RichError> {
        match &from.name {
            parse::CallName::Jet(name) => match Elements::from_str(name.as_inner()) {
                Ok(Elements::CheckSigVerify | Elements::Verify) | Err(_) => {
                    Err(Error::JetDoesNotExist(name.clone())).with_span(from)
                }
                Ok(jet) => Ok(Self::Jet(jet)),
            },
            parse::CallName::UnwrapLeft(right_ty) => scope
                .resolve(right_ty)
                .map(Self::UnwrapLeft)
                .with_span(from),
            parse::CallName::UnwrapRight(left_ty) => scope
                .resolve(left_ty)
                .map(Self::UnwrapRight)
                .with_span(from),
            parse::CallName::IsNone(some_ty) => {
                scope.resolve(some_ty).map(Self::IsNone).with_span(from)
            }
            parse::CallName::Unwrap => Ok(Self::Unwrap),
            parse::CallName::Assert => Ok(Self::Assert),
            parse::CallName::Panic => Ok(Self::Panic),
            parse::CallName::TypeCast(target) => {
                scope.resolve(target).map(Self::TypeCast).with_span(from)
            }
            parse::CallName::Custom(name) => scope
                .get_function(name)
                .cloned()
                .map(Self::Custom)
                .ok_or(Error::FunctionUndefined(name.clone()))
                .with_span(from),
            parse::CallName::Fold(name, bound) => {
                let function = scope
                    .get_function(name)
                    .cloned()
                    .ok_or(Error::FunctionUndefined(name.clone()))
                    .with_span(from)?;
                // A function that is used in a list fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2 || function.params()[1].ty() != function.body().ty()
                {
                    Err(Error::FunctionNotFoldable(name.clone())).with_span(from)
                } else {
                    Ok(Self::Fold(function, *bound))
                }
            }
            parse::CallName::ForWhile(name) => {
                let function = scope
                    .get_function(name)
                    .cloned()
                    .ok_or(Error::FunctionUndefined(name.clone()))
                    .with_span(from)?;
                // A function that is used in a for-while loop has the signature:
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                // where
                //   N is a power of two
                if function.params().len() != 3 {
                    return Err(Error::FunctionNotLoopable(name.clone())).with_span(from);
                }
                match function.body().ty().as_either() {
                    Some((_, out_r)) if out_r == function.params().first().unwrap().ty() => {}
                    _ => {
                        return Err(Error::FunctionNotLoopable(name.clone())).with_span(from);
                    }
                }
                // Disable loops for u32 or higher since no one will want to run
                // 2^32 = 4294967296 ≈ 4 billion iterations.
                // The resulting Simplicity program will not fit into a Bitcoin block.
                match function.params().get(2).unwrap().ty().as_integer() {
                    Some(
                        int_ty @ (UIntType::U1
                        | UIntType::U2
                        | UIntType::U4
                        | UIntType::U8
                        | UIntType::U16),
                    ) => Ok(Self::ForWhile(function, int_ty.bit_width())),
                    _ => Err(Error::FunctionNotLoopable(name.clone())).with_span(from),
                }
            }
        }
    }
}

impl AbstractSyntaxTree for Match {
    type From = parse::Match;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        let scrutinee_ty = from.scrutinee_type();
        let scrutinee_ty = scope.resolve(&scrutinee_ty).with_span(from)?;
        let scrutinee =
            Expression::analyze(from.scrutinee(), &scrutinee_ty, scope).map(Arc::new)?;

        scope.push_scope();
        if let Some((id_l, ty_l)) = from.left().pattern.as_typed_variable() {
            let ty_l = scope.resolve(ty_l).with_span(from)?;
            scope.insert_variable(id_l.clone(), ty_l);
        }
        let ast_l = Expression::analyze(&from.left().expression, ty, scope).map(Arc::new)?;
        scope.pop_scope();
        scope.push_scope();
        if let Some((id_r, ty_r)) = from.right().pattern.as_typed_variable() {
            let ty_r = scope.resolve(ty_r).with_span(from)?;
            scope.insert_variable(id_r.clone(), ty_r);
        }
        let ast_r = Expression::analyze(&from.right().expression, ty, scope).map(Arc::new)?;
        scope.pop_scope();

        Ok(Self {
            scrutinee,
            left: MatchArm {
                pattern: from.left().pattern.clone(),
                expression: ast_l,
            },
            right: MatchArm {
                pattern: from.right().pattern.clone(),
                expression: ast_r,
            },
            span: *from.as_ref(),
        })
    }
}

impl AsRef<Span> for Assignment {
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
