use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;

use either::Either;
use simplicity::jet::Elements;

use crate::error::{Error, RichError, WithSpan};
use crate::parse;
use crate::parse::{Identifier, MatchPattern, Span, WitnessName};
use crate::pattern::Pattern;
use crate::types::{AliasedType, ResolvedType, TypeConstructible, TypeDeconstructible};
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

/// A program is a sequence of statements.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    statements: Arc<[Statement]>,
    witnesses: DeclaredWitnesses,
}

impl Program {
    /// Access the statements of the program.
    pub fn statements(&self) -> &[Statement] {
        &self.statements
    }

    /// Access the map of declared witnesses.
    pub fn witnesses(&self) -> &DeclaredWitnesses {
        &self.witnesses
    }
}

/// A statement is a program component.
///
/// Statements can define variables or type aliases,
/// but they never return values.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// Variable assignment.
    Assignment(Assignment),
    /// Expression that returns nothing (the unit value).
    Expression(Expression),
    /// Type alias.
    ///
    /// The alias was resolved when the abstract syntax tree was created.
    /// We keep the alias statement simply because it is annoying to remove parts of the tree during analysis.
    TypeAlias,
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
    /// A single expression directly returns its value.
    Single(SingleExpression),
    /// A block expression first executes a series of statements inside a local scope,
    /// and then it returns the value of its final expression.
    Block(Arc<[Statement]>, Arc<Expression>),
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
    /// [`Option::unwrap`].
    Unwrap,
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
#[derive(Clone, Debug, Eq, PartialEq)]
struct Scope {
    variables: Vec<HashMap<Identifier, ResolvedType>>,
    aliases: Vec<HashMap<Identifier, ResolvedType>>,
    witnesses: HashMap<WitnessName, ResolvedType>,
}

impl Default for Scope {
    fn default() -> Self {
        Self {
            variables: vec![HashMap::new()],
            aliases: vec![HashMap::new()],
            witnesses: HashMap::new(),
        }
    }
}

impl Scope {
    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
        self.aliases.push(HashMap::new());
    }

    /// Pop the current scope from the stack.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Stack is empty");
        self.aliases.pop().expect("Stack is empty");
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
    /// There are any undefined aliases. The method returns the first such undefined alias.
    pub fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Identifier> {
        let get_alias = |name: &Identifier| -> Option<ResolvedType> {
            self.aliases
                .iter()
                .rev()
                .find_map(|scope| scope.get(name))
                .cloned()
        };
        ty.resolve(get_alias)
    }

    /// Push a type alias onto the current scope.
    ///
    /// ## Errors
    ///
    /// There are any undefined aliases. The method returns the first such undefined alias.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert_alias(&mut self, alias: Identifier, ty: AliasedType) -> Result<(), Identifier> {
        let resolved_ty = self.resolve(&ty)?;
        self.aliases
            .last_mut()
            .expect("Stack is empty")
            .insert(alias, resolved_ty);
        Ok(())
    }

    /// Insert a witness into the global map.
    ///
    /// ## Errors
    ///
    /// The witness name has already been defined somewhere else in the program.
    /// Witness names may be used at most throughout the entire program.
    pub fn insert_witness(&mut self, name: WitnessName, ty: ResolvedType) -> Result<(), Error> {
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
        let statements = from
            .statements
            .iter()
            .map(|s| Statement::analyze(s, &unit, &mut scope))
            .collect::<Result<Arc<[Statement]>, RichError>>()?;
        let witnesses = DeclaredWitnesses(scope.into_witnesses());

        Ok(Self {
            statements,
            witnesses,
        })
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
            parse::Statement::TypeAlias(alias) => {
                scope
                    .insert_alias(alias.name.clone(), alias.ty.clone())
                    .map_err(Error::UndefinedAlias)
                    .with_span(alias)?;
                Ok(Self::TypeAlias)
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
        let ty_expr = scope
            .resolve(&from.ty)
            .map_err(Error::UndefinedAlias)
            .with_span(from)?;
        let typed_variables = from.pattern.is_of_type(&ty_expr).with_span(from)?;
        for (identifier, ty) in typed_variables {
            scope.insert_variable(identifier, ty);
        }
        let expression = Expression::analyze(&from.expression, &ty_expr, scope)?;

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
                let ast_expression = Expression::analyze(expression, ty, scope).map(Arc::new)?;
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
                    .map_err(|_| Error::WitnessReused(name.clone()))
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
            parse::CallName::Jet(name) => Elements::from_str(name.as_inner())
                .map_err(|_| Error::JetDoesNotExist(name.clone()))
                .map(Self::Jet)
                .with_span(from),
            parse::CallName::UnwrapLeft(right_ty) => scope
                .resolve(right_ty)
                .map(Self::UnwrapLeft)
                .map_err(Error::UndefinedAlias)
                .with_span(from),
            parse::CallName::UnwrapRight(left_ty) => scope
                .resolve(left_ty)
                .map(Self::UnwrapRight)
                .map_err(Error::UndefinedAlias)
                .with_span(from),
            parse::CallName::Unwrap => Ok(Self::Unwrap),
        }
    }
}

impl AbstractSyntaxTree for Match {
    type From = parse::Match;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, RichError> {
        let scrutinee_ty = from.scrutinee_type();
        let scrutinee_ty = scope
            .resolve(&scrutinee_ty)
            .map_err(Error::UndefinedAlias)
            .with_span(from)?;
        let scrutinee =
            Expression::analyze(from.scrutinee(), &scrutinee_ty, scope).map(Arc::new)?;

        scope.push_scope();
        if let Some((id_l, ty_l)) = from.left().pattern.as_typed_variable() {
            let ty_l = scope
                .resolve(ty_l)
                .map_err(Error::UndefinedAlias)
                .with_span(from)?;
            scope.insert_variable(id_l.clone(), ty_l);
        }
        let ast_l = Expression::analyze(&from.left().expression, ty, scope).map(Arc::new)?;
        scope.pop_scope();
        scope.push_scope();
        if let Some((id_r, ty_r)) = from.right().pattern.as_typed_variable() {
            let ty_r = scope
                .resolve(ty_r)
                .map_err(Error::UndefinedAlias)
                .with_span(from)?;
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
