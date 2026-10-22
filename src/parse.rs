//! This module contains the parsing code to convert the
//! tokens into an AST.

#[cfg(feature = "arbitrary")]
mod arbitrary_impls;
mod display;
mod grammar;
#[cfg(feature = "fmt")]
mod lossless;
mod pipeline;

pub use self::grammar::ChumskyParse;
#[cfg(feature = "fmt")]
pub use self::lossless::ParsedSource;
pub use self::pipeline::{ParseFromStr, ParseFromStrWithErrors};

use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{any, choice, just, nested_delimiters, recursive, via_parser};
use chumsky::{select, IterParser, Parser};

use either::Either;
use miniscript::iter::{Tree, TreeLike};

use crate::driver::CRATE_STR;
use crate::error::{Diagnostic, Error, Span};
use crate::impl_eq_hash;
use crate::lexer::Token;
use crate::num::NonZeroPow2Usize;
use crate::parse::grammar::{delimited_with_recovery, ParseError};
use crate::pattern::Pattern;
use crate::str::{
    AliasName, Binary, Decimal, FunctionName, Hexadecimal, Identifier, JetName, ModuleName,
    SymbolName,
};
use crate::types::{AliasedType, TypeConstructible};
use crate::unstable::{impl_require_feature, FeatureRequirement, RequireFeature, UnstableFeature};
use crate::TemplateProgramWitness;

/// A program is a sequence of items.
#[derive(Clone, Debug)]
pub struct Program {
    items: Arc<[Item]>,
    span: Span,
}

impl Program {
    // Need for driver usage
    pub(crate) fn new(items: &[Item], span: Span) -> Self {
        Self {
            items: Arc::from(items),
            span,
        }
    }

    /// Access the items of the program.
    pub fn items(&self) -> &[Item] {
        &self.items
    }
}

impl_eq_hash!(Program; items);

impl_require_feature!(Program { recurse: items; });

/// An item is a component of a program.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Item {
    /// A type alias.
    TypeAlias(TypeAlias),
    /// A function.
    Function(Function),
    /// An import declaration (e.g., `use math::add`) that brings another
    /// [`Item`] into the current scope.
    Use(UseDecl),
    /// An enum declaration.
    EnumDeclaration(EnumDeclaration),
    /// A module containing a collection of nested [`Item`].
    Module(Module),
    /// A placeholder used exclusively for error recovery during parsing.
    ///
    /// When the parser encounters a syntax error, it skips the malformed tokens
    /// until it reaches a valid top-level keyword and inserts `Ignored` into the AST.
    Ignored,
}

impl Item {
    /// Access the source span when this item was parsed successfully.
    ///
    /// Error-recovery placeholders have no source node to decorate.
    pub fn span(&self) -> Option<&Span> {
        match self {
            Self::TypeAlias(alias) => Some(alias.span()),
            Self::Function(function) => Some(function.span()),
            Self::Use(use_decl) => Some(use_decl.span()),
            Self::EnumDeclaration(declaration) => Some(declaration.span()),
            Self::Module(module) => Some(module.span()),
            Self::Ignored => None,
        }
    }
}

impl_require_feature!(Item {
    variants:
        TypeAlias(alias),
        Function(function),
        Use(use_decl),
        EnumDeclaration(decl),
        Module(module),
        Ignored,
});

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Visibility {
    Public,
    #[default]
    Private,
}

/// Represents an import declaration in the Abstract Syntax Tree.
///
/// This structure defines how items from other modules or files are brought into the
/// current scope. Note that in this architecture, the first identifier in the path
/// is always treated as an dependency root path name bound to a specific physical path.
///
/// # Example
/// ```text
/// pub use std::collections::{HashMap, HashSet};
/// ```
#[derive(Clone, Debug)]
pub struct UseDecl {
    /// The visibility of the import (e.g., `pub use` vs `use`).
    visibility: Visibility,

    /// The base path to the target file or module.
    ///
    /// The first element is always the registered dependency root path name for
    /// the import path. Subsequent elements represent nested modules or directories.
    path: Vec<Identifier>,

    /// The specific item or list of items being imported from the resolved path.
    items: UseItems,
    span: Span,
}

impl_require_feature!(UseDecl {
    requires: UnstableFeature::Imports, span: span;
    recurse: items;
});

impl_require_feature!(UseItems {
    variants:
        Single(_),
        List(_),
});

impl UseDecl {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Returns the full logical module path as a vector of string slices.
    ///
    /// This includes the Dependency Root Path Name (the first segment)
    /// followed by all subsequent sub-module segments.
    pub fn path(&self) -> &[Identifier] {
        &self.path
    }

    pub fn items(&self) -> &UseItems {
        &self.items
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn str_path(&self) -> String {
        let path: PathBuf = self.path().iter().map(Identifier::as_str).collect();
        path.display().to_string()
    }

    /// Extracts the Dependency Root Path Name (the very first segment) from this path.
    ///
    /// # Errors
    ///
    /// Returns a `Diagnostic` if the use declaration path is completely empty.
    pub fn drp_name(&self) -> Result<&str, Diagnostic> {
        let parts: Vec<&str> = self.path().iter().map(Identifier::as_str).collect();
        parts.first().copied().ok_or_else(|| {
            Error::CannotParse {
                msg: "Empty use path".to_string(),
            }
            .with_span(self.span)
        })
    }

    pub(crate) fn set_path(&mut self, path: &[Identifier]) {
        self.path = Vec::from(path)
    }
}

// `span` are required because `UseDecl` hashing is context-dependent.
// For instance, identical `use crate::...` paths differ between binary and library roots.
// Tested by: `functional_tests::identical_crate_uses_in_different_package_roots_do_not_poison_resolution_cache`.
impl_eq_hash!(UseDecl; visibility, path, items, span);

/// Aliases the specific identifier of an imported type to a new, local identifier
pub type AliasedSymbolName = (SymbolName, Option<SymbolName>);

/// Specified the items being brought into scope at the end of a `use` declaration
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum UseItems {
    /// A single item import.
    ///
    /// # Example
    /// ```text
    /// use core::math::add;
    /// ```
    Single(AliasedSymbolName),

    /// A multiple item import grouped in a list.
    ///
    /// # Example
    /// ```text
    /// use core::math::{add, subtract};
    /// ```
    List(Vec<AliasedSymbolName>),
}

#[derive(Clone, Debug)]
pub struct Function {
    visibility: Visibility,
    name: FunctionName,
    params: Arc<[FunctionParam]>,
    ret: Option<AliasedType>,
    body: Expression,
    span: Span,
}

impl Function {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the name of the function.
    pub fn name(&self) -> &FunctionName {
        &self.name
    }

    /// Access the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the return type of the function.
    ///
    /// An empty return type means that the function returns the unit value.
    pub fn ret(&self) -> Option<&AliasedType> {
        self.ret.as_ref()
    }

    /// Access the body of the function.
    pub fn body(&self) -> &Expression {
        &self.body
    }

    /// Access the span of the function.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Function; visibility, name, params, ret, body);

impl_require_feature!(Function { recurse: params, ret, body; });

/// Parameter of a function.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct FunctionParam {
    identifier: Identifier,
    ty: AliasedType,
    span: Span,
}

impl FunctionParam {
    /// Access the identifier of the parameter.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// Access the type of the parameter.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the source span of the complete parameter.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(FunctionParam; identifier, ty);

impl_require_feature!(FunctionParam { recurse: ty; });

/// A statement is a component of a block expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// An expression that returns nothing (the unit value).
    Expression(Expression),
}

impl Statement {
    /// Access the span of the statement contents.
    ///
    /// The terminating semicolon is deliberately not part of this span: it is a
    /// separator owned by the containing block's layout.
    pub fn span(&self) -> &Span {
        match self {
            Self::Assignment(assignment) => assignment.span(),
            Self::Expression(expression) => expression.span(),
        }
    }
}

impl_require_feature!(Statement {
    variants:
        Assignment(assignment),
        Expression(expr),
});

/// The output of an expression is assigned to a pattern.
#[derive(Clone, Debug)]
pub struct Assignment {
    pattern: Pattern,
    ty: AliasedType,
    expression: Expression,
    span: Span,
}

impl Assignment {
    /// Access the pattern of the assignment.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Access the return type of assigned expression.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the assigned expression.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Assignment; pattern, ty, expression);

impl_require_feature!(Assignment { recurse: pattern, ty, expression; });

/// Call expression.
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

    /// Access the arguments to the call.
    pub fn args(&self) -> &[Expression] {
        self.args.as_ref()
    }

    /// Access the span of the call.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Call; name, args);

// Hand-written because `raw_hash` is gated per call name, while the macro
// can gate only an entire type, and `CallName` has no span of its own.
impl RequireFeature for Call {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
        if let CallName::RawHash(_) = self.name {
            out.push(FeatureRequirement::new(UnstableFeature::RawHash, self.span));
        }

        self.name.feature_requirements(out);
        self.args.feature_requirements(out);
    }
}

/// Name of a call.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum CallName {
    /// Name of a jet.
    Jet(JetName),
    /// [`Either::unwrap_left`].
    UnwrapLeft(AliasedType),
    /// [`Either::unwrap_right`].
    UnwrapRight(AliasedType),
    /// [`Option::unwrap`].
    Unwrap,
    /// [`Option::is_none`].
    IsNone(AliasedType),
    /// [`assert!`].
    Assert,
    /// [`panic!`] without error message.
    Panic,
    /// [`dbg!`].
    Debug,
    /// Cast from the given source type.
    TypeCast(AliasedType),
    /// Name of a custom function.
    Custom(FunctionName),
    /// Fold of a bounded list with the given function.
    Fold(FunctionName, NonZeroPow2Usize),
    /// Fold of an array with the given function.
    ArrayFold(FunctionName, NonZeroUsize),
    /// Loop over the given function a bounded number of times until it returns success.
    ForWhile(FunctionName),
    /// SHA-256 of the concatenated bytes of a tuple of unsigned integers of the given type.
    RawHash(AliasedType),
}

impl_require_feature!(CallName {
    variants:
        Jet(_),
        UnwrapLeft(ty),
        UnwrapRight(ty),
        Unwrap,
        IsNone(ty),
        Assert,
        Panic,
        Debug,
        TypeCast(ty),
        Custom(_),
        Fold(_, _),
        ArrayFold(_, _),
        ForWhile(_),
        RawHash(ty),
});

/// A type alias.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct TypeAlias {
    visibility: Visibility,
    name: AliasName,
    ty: AliasedType,
    span: Span,
}

impl TypeAlias {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the name of the alias.
    pub fn name(&self) -> &AliasName {
        &self.name
    }

    /// Access the type that the alias resolves to.
    ///
    /// During the parsing stage, the resolved type may include aliases.
    /// The compiler will later check if all contained aliases have been declared before.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the span of the alias.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(TypeAlias; name, ty);

impl_require_feature!(TypeAlias { recurse: ty; });

/// A single variant in an enum declaration.
///
/// A variant's position among the declared variants determines its leaf
/// in the enum's balanced sum, i.e. its wire encoding.
/// A variant may carry payload types (`Refresh(Signature, u8)`).
/// A variant without payload is a unit variant.
#[derive(Clone, Debug)]
pub struct EnumVariant {
    name: Identifier,
    payload: Arc<[AliasedType]>,
    span: Span,
}

impl EnumVariant {
    pub fn name(&self) -> &Identifier {
        &self.name
    }

    /// Access the payload types of the variant. Empty for unit variants.
    pub fn payload(&self) -> &[AliasedType] {
        &self.payload
    }

    /// Access the source span of the complete variant.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumVariant; name, payload);

impl AsRef<Span> for EnumVariant {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// An enum declaration.
#[derive(Clone, Debug)]
pub struct EnumDeclaration {
    visibility: Visibility,
    name: AliasName,
    variants: Arc<[EnumVariant]>,
    span: Span,
}

impl EnumDeclaration {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    pub fn name(&self) -> &AliasName {
        &self.name
    }

    pub fn variants(&self) -> &[EnumVariant] {
        &self.variants
    }

    /// Access the source span of the complete declaration.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_require_feature!(EnumVariant { recurse: payload; });

impl_require_feature!(EnumDeclaration {
    requires: UnstableFeature::Enums, span: span;
    recurse: variants;
});

impl_eq_hash!(EnumDeclaration; name, variants);

impl AsRef<Span> for EnumDeclaration {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// An expression is something that returns a value.
#[derive(Clone, Debug)]
pub struct Expression {
    inner: ExpressionInner,
    span: Span,
}

impl Expression {
    /// Access the inner expression.
    pub fn inner(&self) -> &ExpressionInner {
        &self.inner
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Convert the expression into a block expression.
    #[cfg(feature = "arbitrary")]
    fn into_block(self) -> Self {
        match self.inner {
            ExpressionInner::Single(_) => Expression {
                span: self.span,
                inner: ExpressionInner::Block(Arc::from([]), Some(Arc::new(self))),
            },
            _ => self,
        }
    }

    pub fn empty(span: Span) -> Self {
        Self {
            inner: ExpressionInner::Single(SingleExpression {
                inner: SingleExpressionInner::Tuple(Arc::new([])),
                span,
            }),
            span,
        }
    }
}

impl_eq_hash!(Expression; inner);

impl_require_feature!(Expression { recurse: inner; });

/// The kind of expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionInner {
    /// A single expression directly returns a value.
    Single(SingleExpression),
    /// A block expression first executes a series of statements inside a local scope.
    /// Then, the block returns the value of its final expression.
    /// The block returns nothing (unit) if there is no final expression.
    Block(Arc<[Statement]>, Option<Arc<Expression>>),
}

impl_require_feature!(ExpressionInner {
    variants:
        Single(single),
        Block(statements, maybe_expr),
});

/// A single expression directly returns a value.
#[derive(Clone, Debug)]
pub struct SingleExpression {
    inner: SingleExpressionInner,
    span: Span,
}

impl SingleExpression {
    /// Access the inner expression.
    pub fn inner(&self) -> &SingleExpressionInner {
        &self.inner
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(SingleExpression; inner);

impl_require_feature!(SingleExpression {recurse: inner; });

/// The kind of single expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SingleExpressionInner {
    /// Either wrapper expression
    Either(Either<Arc<Expression>, Arc<Expression>>),
    /// Option wrapper expression
    Option(Option<Arc<Expression>>),
    /// Boolean literal expression
    Boolean(bool),
    /// Decimal string literal.
    Decimal(Decimal),
    /// Binary string literal.
    Binary(Binary),
    /// Hexadecimal string literal.
    Hexadecimal(Hexadecimal),
    /// Witness value.
    Witness(TemplateProgramWitness),
    /// Parameter value.
    Parameter(TemplateProgramWitness),
    /// Variable identifier expression
    Variable(Identifier),
    /// Function call
    Call(Call),
    /// Expression in parentheses
    Expression(Arc<Expression>),
    /// Match expression over a sum type
    Match(Match),
    /// Match expression over an enum's variants
    EnumMatch(EnumMatch),
    /// Construction of an enum variant
    EnumConstruction(EnumConstruction),
    /// Tuple wrapper expression
    Tuple(Arc<[Expression]>),
    /// Array wrapper expression
    Array(Arc<[Expression]>),
    /// List wrapper expression
    ///
    /// The exclusive upper bound on the list size is not known at this point
    List(Arc<[Expression]>),
}

impl_require_feature!(SingleExpressionInner {
    variants:
        Either(either),
        Option(maybe_expr),
        Boolean(_),
        Decimal(_),
        Binary(_),
        Hexadecimal(_),
        Witness(_),
        Parameter(_),
        Variable(_),
        Call(call),
        Expression(expr),
        Match(match_),
        EnumMatch(enum_match),
        EnumConstruction(construction),
        Tuple(exprs),
        Array(exprs),
        List(exprs),
});

/// Match expression.
#[derive(Clone, Debug)]
pub struct Match {
    scrutinee: Arc<Expression>,
    left: MatchArm,
    right: MatchArm,
    span: Span,
}

impl Match {
    /// Access the expression that is matched.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the match arm for left sum values.
    pub fn left(&self) -> &MatchArm {
        &self.left
    }

    /// Access the match arm for right sum values.
    pub fn right(&self) -> &MatchArm {
        &self.right
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Get the type of the expression that is matched.
    pub fn scrutinee_type(&self) -> AliasedType {
        match (&self.left.pattern, &self.right.pattern) {
            (MatchPattern::Left(_, ty_l), MatchPattern::Right(_, ty_r)) => {
                AliasedType::either(ty_l.clone(), ty_r.clone())
            }
            (MatchPattern::None, MatchPattern::Some(_, ty_r)) => AliasedType::option(ty_r.clone()),
            (MatchPattern::False, MatchPattern::True) => AliasedType::boolean(),
            _ => unreachable!("Match expressions have valid left and right arms"),
        }
    }
}

impl_eq_hash!(Match; scrutinee, left, right);

impl_require_feature!(Match {recurse: scrutinee, left, right; });

/// Match expression over a named enum type.
#[derive(Clone, Debug)]
pub struct EnumMatch {
    scrutinee: Arc<Expression>,
    arms: Arc<[EnumMatchArm]>,
    span: Span,
}

impl EnumMatch {
    /// Access the expression that is matched.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the match arms.
    pub fn arms(&self) -> &[EnumMatchArm] {
        &self.arms
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_require_feature!(EnumMatch {
    requires: UnstableFeature::Enums, span: span;
    recurse: scrutinee, arms;
});

impl_eq_hash!(EnumMatch; scrutinee, arms);

impl AsRef<Span> for EnumMatch {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// Arm of an enum match expression: `Enum::Variant(bindings..) => expression`.
///
/// The arm type carries the classification the parser proved.
/// Every arm of an [`EnumMatch`] names an enum variant, so no other pattern kind is representable here.
#[derive(Clone, Debug)]
pub struct EnumMatchArm {
    enum_path: Arc<[Identifier]>,
    variant: Identifier,
    bindings: Arc<[(Pattern, AliasedType)]>,
    expression: Arc<Expression>,
    span: Span,
}

impl EnumMatchArm {
    /// Access the written enum path of the arm, e.g. `["m", "Choice"]`.
    pub fn enum_path(&self) -> &[Identifier] {
        &self.enum_path
    }

    /// The written enum path as one string, e.g. `m::Choice`.
    pub fn enum_path_string(&self) -> String {
        self.enum_path
            .iter()
            .map(Identifier::as_str)
            .collect::<Vec<_>>()
            .join("::")
    }

    /// Access the name of the matched variant.
    pub fn variant(&self) -> &Identifier {
        &self.variant
    }

    /// Access the payload bindings of the arm. Empty for unit variants.
    pub fn bindings(&self) -> &[(Pattern, AliasedType)] {
        &self.bindings
    }

    /// Access the expression that is executed in the match arm.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the source span of the complete arm, including its optional comma.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumMatchArm; enum_path, variant, bindings, expression);

impl_require_feature!(EnumMatchArm { recurse: expression; });

/// Construction of an enum variant: `Action::Refresh(sig, 3)`.
///
/// The written enum name is either an alias in scope (`MyChoice`) or the
/// enum's declared name itself (`Action`), which needs no scope.
/// Unit variants take no argument list.
#[derive(Clone, Debug)]
pub struct EnumConstruction {
    enum_path: Arc<[Identifier]>,
    variant: Identifier,
    args: Arc<[Expression]>,
    span: Span,
}

impl EnumConstruction {
    /// Access the written enum path, e.g. `["m", "Action"]`.
    pub fn enum_path(&self) -> &[Identifier] {
        &self.enum_path
    }

    /// Access the name of the constructed variant.
    pub fn variant(&self) -> &Identifier {
        &self.variant
    }

    /// Access the payload arguments. Empty for unit variants.
    pub fn args(&self) -> &[Expression] {
        &self.args
    }

    /// Access the span of the construction expression.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// The written enum path as one string, e.g. `m::Action`.
    pub fn enum_path_string(&self) -> String {
        self.enum_path
            .iter()
            .map(Identifier::as_str)
            .collect::<Vec<_>>()
            .join("::")
    }
}

impl_eq_hash!(EnumConstruction; enum_path, variant, args);

impl_require_feature!(EnumConstruction {
    requires: UnstableFeature::Enums, span: span;
    recurse: args;
});

impl AsRef<Span> for EnumConstruction {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// Arm of a match expression.
#[derive(Clone, Debug)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
    span: Span,
}

impl MatchArm {
    /// Access the pattern that guards the match arm.
    pub fn pattern(&self) -> &MatchPattern {
        &self.pattern
    }

    /// Access the expression that is executed in the match arm.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the source span of the complete arm, including its optional comma.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(MatchArm; pattern, expression);

impl_require_feature!(MatchArm {recurse: pattern, expression; });

/// Pattern of a match arm.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum MatchPattern {
    /// Bind inner value of left value to a pattern.
    Left(Pattern, AliasedType),
    /// Bind inner value of right value to a pattern.
    Right(Pattern, AliasedType),
    /// Match none value (no binding).
    None,
    /// Bind inner value of some value to a pattern.
    Some(Pattern, AliasedType),
    /// Match false value (no binding).
    False,
    /// Match true value (no binding).
    True,
}

impl_require_feature!(MatchPattern {
    variants:
        Left(pattern, ty),
        Right(pattern, ty),
        None,
        Some(pattern, ty),
        False,
        True,
});

impl MatchPattern {
    /// Access the pattern of a match pattern that binds a variables.
    pub fn as_pattern(&self) -> Option<&Pattern> {
        match self {
            MatchPattern::Left(i, _) | MatchPattern::Right(i, _) | MatchPattern::Some(i, _) => {
                Some(i)
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }

    /// Access the pattern and the type of a match pattern that binds a variables.
    pub fn as_typed_pattern(&self) -> Option<(&Pattern, &AliasedType)> {
        match self {
            MatchPattern::Left(i, ty) | MatchPattern::Right(i, ty) | MatchPattern::Some(i, ty) => {
                Some((i, ty))
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Module {
    visibility: Visibility,
    name: ModuleName,
    items: Arc<[Item]>,
    span: Span,
}

impl_require_feature!(Module {
    requires: UnstableFeature::Imports, span: span;
    recurse: items;
});

impl Module {
    /// Needed by the driver to wrap a single file into a module.
    pub(crate) fn new(
        file_id: usize,
        visibility: Visibility,
        name: ModuleName,
        items: &[Item],
    ) -> Module {
        Self {
            visibility,
            name,
            items: Arc::from(items),
            span: Span::new(file_id, 0..0),
        }
    }

    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the name of the module.
    pub fn name(&self) -> &ModuleName {
        &self.name
    }

    /// Access the assignments of the module.
    pub fn items(&self) -> &[Item] {
        &self.items
    }

    /// Access the span of the module.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

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
    EnumConstruction(&'a EnumConstruction),
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
                S::Boolean(_)
                | S::Binary(_)
                | S::Decimal(_)
                | S::Hexadecimal(_)
                | S::Variable(_)
                | S::Witness(_)
                | S::Parameter(_)
                | S::Option(None) => Tree::Nullary,
                S::Option(Some(l))
                | S::Either(Either::Left(l))
                | S::Either(Either::Right(l))
                | S::Expression(l) => Tree::Unary(Self::Expression(l)),
                S::Call(call) => Tree::Unary(Self::Call(call)),
                S::Match(match_) => Tree::Unary(Self::Match(match_)),
                S::EnumMatch(enum_match) => Tree::Unary(Self::EnumMatch(enum_match)),
                S::EnumConstruction(construction) => {
                    Tree::Unary(Self::EnumConstruction(construction))
                }
                S::Tuple(elements) | S::Array(elements) | S::List(elements) => {
                    Tree::Nary(elements.iter().map(Self::Expression).collect())
                }
            },
            Self::Call(call) => Tree::Nary(call.args().iter().map(Self::Expression).collect()),
            Self::EnumConstruction(construction) => {
                Tree::Nary(construction.args().iter().map(Self::Expression).collect())
            }
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
                            .map(|arm| Self::Expression(arm.expression())),
                    )
                    .collect(),
            ),
        }
    }
}

impl ChumskyParse for Program {
    /// Parses a sequence of top-level [`Item`]s into a complete [`Program`].
    ///
    /// If an invalid item is encountered, it will safely skip the broken tokens
    /// until it finds a synchronization point. This prevents the parser from
    /// failing completely, allowing it to report multiple syntax errors across the file
    /// while substituting the unparseable sections with [`Item::Ignored`].
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let skip_until_next_item = any()
            .then(
                any()
                    .filter(|t| {
                        !matches!(
                            t,
                            Token::Pub
                                | Token::Use
                                | Token::Fn
                                | Token::Type
                                | Token::Mod
                                | Token::Enum
                        )
                    })
                    .repeated(),
            )
            .map_with(|_, _| Item::Ignored);

        Item::parser()
            .recover_with(via_parser(skip_until_next_item))
            .repeated()
            .collect::<Vec<Item>>()
            .map_with(|items, e| Program {
                items: Arc::from(items),
                span: e.span(),
            })
    }
}

impl ChumskyParse for Item {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|item| {
            let func_parser = Function::parser().map(Item::Function);
            let type_parser = TypeAlias::parser().map(Item::TypeAlias);
            let use_parser = UseDecl::parser().map(Item::Use);
            let enum_parser = EnumDeclaration::parser().map(Item::EnumDeclaration);

            // Lazy item here
            let mod_parser = Module::parser_with_items(item).map(Item::Module);

            choice((
                func_parser,
                use_parser,
                type_parser,
                enum_parser,
                mod_parser,
            ))
        })
    }
}

impl ChumskyParse for Function {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default)
            .labelled("function visibility");

        let params = delimited_with_recovery(
            FunctionParam::parser()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<_>>(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(Arc::from)
        .labelled("function parameters");

        let ret = just(Token::Arrow)
            .ignore_then(AliasedType::parser())
            .or_not()
            .labelled("return type");

        let body = just(Token::LBrace)
            .rewind()
            .ignore_then(Expression::parser())
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                Expression::empty,
            )))
            .labelled("function body");

        visibility
            .then_ignore(just(Token::Fn))
            .then(FunctionName::parser())
            .then(params)
            .then(ret)
            .then(body)
            .map_with(|((((visibility, name), params), ret), body), e| Self {
                visibility,
                name,
                params,
                ret,
                body,
                span: e.span(),
            })
    }
}

impl ChumskyParse for UseDecl {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        let first_segment = select! {
            Token::Ident(ident) => Identifier::from_str_unchecked(ident),
            Token::Crate => Identifier::from_str_unchecked(CRATE_STR),
        };

        // Parse the base path prefix (e.g., `dependency_root_path::file::`, `dependency_root_path::dir::file::`,
        // or `crate::dir::file::`). We require at least 2 segments here because a valid import needs a minimum
        // of 3 items total: the dependency root path (or `crate`), the file, and the specific item.
        //
        // With the introduction of `mod` keyword and single-file flattening, 2 total segments are now
        // valid: `crate::item`, where `crate` is the program root.
        let path = first_segment
            .then_ignore(just(Token::DoubleColon))
            .then(
                Identifier::parser()
                    .then_ignore(just(Token::DoubleColon))
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map(|(first, mut rest)| {
                let mut path = vec![first];
                path.append(&mut rest);
                path
            });

        let aliased_item =
            SymbolName::parser().then(just(Token::As).ignore_then(SymbolName::parser()).or_not());

        let list = aliased_item
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(UseItems::List);
        let single = aliased_item.map(UseItems::Single);
        let items = choice((list, single));

        visibility
            .then_ignore(just(Token::Use))
            .then(path)
            .then(items)
            .then_ignore(just(Token::Semi))
            .map_with(|((visibility, path), items), e| Self {
                visibility,
                path,
                items,
                span: e.span(),
            })
    }
}

impl ChumskyParse for FunctionParam {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let identifier = Identifier::parser();

        let ty = AliasedType::parser();

        identifier
            .then_ignore(just(Token::Colon))
            .then(ty)
            .map_with(|(identifier, ty), e| Self {
                identifier,
                ty,
                span: e.span(),
            })
    }
}

impl Module {
    pub fn parser_with_items<'tokens, 'src: 'tokens, I>(
        item_parser: impl Parser<'tokens, I, Item, ParseError<'src>> + Clone + 'tokens,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        let name = ModuleName::parser().map_with(|name, e| (name, e.span()));

        let items = item_parser
            .repeated()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                |_| Vec::new(),
            )))
            .map(Arc::from);

        visibility
            .then(just(Token::Mod).ignore_then(name).then(items))
            .map_with(|(visibility, (name, items)), e| Self {
                visibility,
                name: name.0,
                items,
                span: e.span(),
            })
            .validate(|module, _, emit| {
                // TODO: Enums may only be declared at the top level of a file (done so to reduce scope of the PR).
                // The bare name is the enum's identity in the ABI, and a module path would obscure it.
                // Direct children suffice. Nested modules validate their own items.
                for item in module.items.iter() {
                    if let Item::EnumDeclaration(decl) = item {
                        emit.emit(
                            Error::Grammar {
                                msg: format!(
                                    "enum `{}` is declared inside `mod {}`; enums may \
                                     only be declared at the top level of a file",
                                    decl.name(),
                                    module.name
                                ),
                            }
                            .with_span(decl.into()),
                        );
                    }
                }
                module
            })
    }
}

impl<'a, A: AsRef<Span>> From<&'a A> for Span {
    fn from(value: &'a A) -> Self {
        *value.as_ref()
    }
}

impl AsRef<Span> for Program {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Function {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for FunctionParam {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Assignment {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for TypeAlias {
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

impl AsRef<Span> for UseDecl {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Module {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

#[cfg(test)]
mod type_alias {
    use super::*;

    #[test]
    fn test_reject_redefined_builtin_type() {
        let ty = TypeAlias::parse_from_str("type Ctx8 = u32")
            .expect_err("Redefining built-in alias should be rejected");

        assert!(ty
            .error()
            .to_string()
            .contains("Type alias `Ctx8` is already exists as built-in alias"));
    }

    #[test]
    fn test_fragment_rejects_version_directive() {
        let err = TypeAlias::parse_from_str("simc \"*\"; type Ctx8 = u32")
            .expect_err("a version directive must not be accepted in a fragment");

        assert!(matches!(err.error(), Error::ReservedSimcKeyword));
    }
}

#[cfg(test)]
mod regular_parsing {
    use crate::driver::MAIN_MODULE;
    use crate::error::DiagnosticManager;
    use crate::parse::grammar::RESERVED_PATTERN_NAMES;
    use crate::{parse, UnstableFeatures};

    use super::*;

    impl UseDecl {
        /// Creates a dummy `UseDecl` specifically for testing `DependencyMap` resolution.
        pub fn dummy_path(path: Vec<Identifier>) -> Self {
            Self {
                visibility: Visibility::default(),
                path,
                items: UseItems::List(Vec::new()),
                span: Span::DUMMY,
            }
        }
    }

    #[test]
    fn test_double_colon() {
        let input = "fn main() { let ab: u8 = <(u4, u4)> : :into((0b1011, 0b1101)); }";
        let mut diagnostics = DiagnosticManager::new();

        let parsed_program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            input,
            &UnstableFeatures::all(),
            &mut diagnostics,
        );

        assert!(parsed_program.is_none());
        assert!(diagnostics.to_string().contains("Expected '::', found ':'"));
    }

    #[test]
    fn test_double_double_colon() {
        let input = "fn main() { let pk: Pubkey = witnes::::PK; }";
        let mut diagnostics = DiagnosticManager::new();

        let parsed_program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            input,
            &UnstableFeatures::all(),
            &mut diagnostics,
        );

        assert!(parsed_program.is_none());
        assert!(
            diagnostics
                .to_string()
                .contains("Expected identifier, found ::"),
            "the second :: should be reported as the error site"
        );
    }

    /// Parse `input` and return whether it was rejected and the collected error text.
    fn parse_with(input: &str, features: &UnstableFeatures) -> (bool, String) {
        let mut diagnostics = DiagnosticManager::new();
        let program =
            Program::parse_from_str_with_errors(MAIN_MODULE, input, features, &mut diagnostics);

        let rejected = program.is_none();
        let text = diagnostics.to_string();

        (rejected, text)
    }

    /// Nested blocks must parse in time linear in their depth.
    #[test]
    fn nested_blocks_parse_without_exponential_backtracking() {
        let depth = 32;
        let input = format!(
            "fn main() {{\n    let x: u32 = {}0{};\n    assert!(jet::eq_32(x, 0));\n}}",
            "{".repeat(depth),
            "}".repeat(depth)
        );

        let (rejected, text) = parse_with(&input, &UnstableFeatures::all());
        assert!(!rejected, "nested blocks must parse: {text}");
    }

    #[test]
    fn inverted_empty_span_from_token_gap_does_not_panic() {
        // Fuzz-found (compile_text).
        //
        // The input is irreducible. The broken `fn` prefix forces the parser into delimiter recovery.
        // The only path that requests an empty span at a lex-error gap and the
        // NUL after `enum` creates that gap.
        // Chumsky builds such spans as `next_token.start .. previous_token.end`, which is inverted
        // across the gap and panicked the strict `Span` constructor.
        //
        // Simplifying any part (even NUL to a space) loses the crash.
        let src = "fn`u({?\u{12}$0;;enum\0===lHf\u{15}";
        let mut diagnostics = DiagnosticManager::new();
        let program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            src,
            &UnstableFeatures::all(),
            &mut diagnostics,
        );

        assert!(program.is_none(), "garbage input must be rejected");
        assert!(diagnostics.has_errors());
    }

    #[test]
    fn recovery_synchronizes_at_enum_declaration() {
        // Discriminating setup: an invalid prefix followed by a malformed
        // enum. Without `Token::Enum` in the synchronization set the whole
        // enum is swallowed into the prefix's recovery span and only one
        // error is reported; with it, the enum parses as its own item and
        // its malformation is reported as a second error.
        let mut diagnostics = DiagnosticManager::new();
        let program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            "let invalid = 1;\nenum Action { A B }\nfn main() {}",
            &UnstableFeatures::all(),
            &mut diagnostics,
        );
        assert!(program.is_none(), "the invalid program must be rejected");
        assert_eq!(
            2,
            diagnostics.error_count(),
            "the invalid prefix and the malformed enum must each report an error"
        );
    }

    #[test]
    fn recovery_after_malformed_enum_reaches_next_item() {
        let (rejected, _text) = parse_with(
            "enum Action { A B }\nfn main() {}",
            &UnstableFeatures::all(),
        );
        assert!(rejected, "a malformed enum must fail compilation");
    }

    #[test]
    fn malformed_construct_containing_enum_keyword_reports_errors() {
        // `enum` inside a badly malformed nested construct may be mistaken
        // for an item boundary; compilation must still fail cleanly.
        let (rejected, _text) = parse_with(
            "fn broken() { let x = (enum; }\nfn main() {}",
            &UnstableFeatures::all(),
        );
        assert!(rejected, "a malformed construct must fail compilation");
    }

    #[test]
    fn test_gated_syntax_is_rejected_without_features() {
        // Real `use`/`mod` syntax: rejected under none() (naming the feature + a
        // -Z hint), accepted under all(). Delete when `imports` stabilizes.
        for input in [
            "use crate::foo::bar;\nfn main() { }",
            "mod inner { }\nfn main() { }",
        ] {
            let (rejected, error) = parse_with(input, &UnstableFeatures::none());
            assert!(
                rejected,
                "gated syntax must be rejected without features (if this feature was \
                 just stabilized, delete this test):\n{input}"
            );
            assert!(
                error.contains("imports") && error.contains("-Z"),
                "rejection should name the feature and suggest -Z, got:\n{error}"
            );

            let (rejected, error) = parse_with(input, &UnstableFeatures::all());
            assert!(
                !rejected,
                "the same syntax must parse with all features enabled:\n{error}"
            );
        }
    }

    #[test]
    fn test_type_heavy_program_needs_no_features() {
        // Types are traversed by `RequireFeature` but not gated, so a type-heavy,
        // import-free program must parse with no features (no false-positive gates).
        let input = r#"type Alias = u32;
fn pick(e: Either<u32, u32>) -> u32 {
    match e {
        Left(a: u32) => a,
        Right(b: u32) => b,
    }
}
fn main() {
    let casted: u32 = <(u16, u16)>::into((0xbeef, 0xbabe));
    let chosen: Alias = pick(Left(casted));
    assert!(jet::eq_32(chosen, chosen));
}
"#;
        // `parse_from_str_with_errors` returns `Some` only when no errors were
        // collected, so a non-rejection already proves there were no gate errors.
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(
            !rejected,
            "type-heavy but import-free program should parse with no features:\n{error}"
        );
    }

    #[test]
    fn test_syntax_error_does_not_produce_spurious_feature_gate_error() {
        // The gate check skips error-recovered ASTs, so a program with
        // both a syntax error and gated syntax reports only the syntax error.
        let input = "use crate::foo;\nfn main( {";
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(rejected, "broken program must be rejected");
        assert!(
            !error.contains("-Z"),
            "syntax error should not produce a spurious feature-gate hint, got:\n{error}"
        );
    }

    #[test]
    fn test_lexer_error_does_not_produce_spurious_feature_gate_error() {
        // Lexer-side companion to the case above: the stray `@` lexes with an
        // error but recovers a cleanly-parsing `use` AST, and a program that
        // didn't lex cleanly skips the gate check — so no spurious `-Z` hint.
        let input = "use crate@::foo;\nfn main() { }";
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(rejected, "program with a lexer error must be rejected");
        assert!(
            !error.contains("-Z"),
            "lexer error should not produce a spurious feature-gate hint, got:\n{error}"
        );
    }

    #[test]
    fn test_use_decl_display_round_trips_with_aliases() {
        for input in [
            "use lib::A::foo;",
            "use lib::A::foo as bar;",
            "use lib::A::{foo, bar as baz};",
        ] {
            let program = parse::Program::parse_from_str(input).expect("parsing works");
            assert_eq!(program.to_string(), format!("{input}\n"));
        }
    }

    #[test]
    fn statement_spans_exclude_terminating_semicolons() {
        let input = "fn main() { let value: u8 = 0; value; }";
        let program = Program::parse_from_str(input).expect("program parses");

        let Item::Function(function) = &program.items()[0] else {
            panic!("expected a function item");
        };
        let ExpressionInner::Block(statements, None) = function.body().inner() else {
            panic!("expected a block containing only statements");
        };

        assert_eq!(
            statements[0].span().to_slice(input),
            Some("let value: u8 = 0")
        );
        assert_eq!(statements[1].span().to_slice(input), Some("value"));
    }

    fn parse_item(input: &str) -> Item {
        let program = parse::Program::parse_from_str(input).expect("parsing should succeed");
        program.items().first().expect("expected one item").clone()
    }

    #[test]
    fn test_enum_declaration_basic() {
        let item = parse_item("enum Path { Inherit, ColdSpend, RefreshSpend, }");
        let Item::EnumDeclaration(decl) = item else {
            panic!("expected EnumDeclaration, got {item:?}");
        };
        assert_eq!(decl.name(), "Path");
        assert_eq!(decl.variants().len(), 3);
        assert_eq!(decl.variants()[0].name(), "Inherit");
        assert_eq!(decl.variants()[2].name(), "RefreshSpend");
    }

    #[test]
    fn test_enum_declaration_pub() {
        let item = parse_item("pub enum Color { Red, Green, Blue, }");
        let Item::EnumDeclaration(decl) = item else {
            panic!("expected EnumDeclaration");
        };
        assert_eq!(decl.visibility(), &Visibility::Public);
        assert_eq!(decl.name(), "Color");
    }

    #[test]
    fn test_enum_declaration_display_round_trip() {
        let input = "enum Path { Inherit, ColdSpend, RefreshSpend, }";
        let item = parse_item(input);
        let Item::EnumDeclaration(decl) = item else {
            panic!("expected EnumDeclaration");
        };
        assert_eq!(
            decl.to_string(),
            "enum Path { Inherit, ColdSpend, RefreshSpend, }"
        );
    }

    #[test]
    fn test_enum_declaration_reserved_name() {
        for reserved in RESERVED_PATTERN_NAMES {
            let result = Program::parse_from_str(&format!("enum {reserved} {{ A, B, }}"));
            let error = result.expect_err(&format!("enum name {reserved} is reserved"));
            assert!(
                error.to_string().contains("reserved"),
                "error should say the name is reserved: {error}"
            );
        }
    }
}

#[cfg(test)]
#[cfg(feature = "fmt")]
mod fmt_parsing {
    use crate::driver::MAIN_MODULE;
    use crate::error::DiagnosticManager;
    use crate::parse::grammar::RESERVED_PATTERN_NAMES;
    use crate::parse::lossless::ParsedSource;
    use crate::UnstableFeatures;

    use super::*;

    /// Parse `input`, appending any formatter diagnostics to `diagnostics`.
    fn parse_with_diagnostics<'src>(
        input: &'src str,
        features: &UnstableFeatures,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<ParsedSource<'src>> {
        Program::parse_with_errors_for_fmt(MAIN_MODULE, input, features, diagnostics)
    }

    /// Parse `input` and return whether it was rejected and the collected error text.
    fn parse_with(input: &str, features: &UnstableFeatures) -> (bool, String) {
        let mut diagnostics = DiagnosticManager::new();
        let program = parse_with_diagnostics(input, features, &mut diagnostics);

        let rejected = program.is_none();
        let text = diagnostics.to_string();

        (rejected, text)
    }

    /// Parse `input` and return whether it was rejected and the collected error in `DiagnosticManager`.
    fn parse_with_diagnosis(input: &str, features: &UnstableFeatures) -> (bool, DiagnosticManager) {
        let mut diagnostics = DiagnosticManager::new();
        let program = parse_with_diagnostics(input, features, &mut diagnostics);

        let rejected = program.is_none();

        (rejected, diagnostics)
    }

    /// Parse `input` and return whether it was rejected and the collected error text together with `ParsedSource`.
    fn parse_with_extended_out<'src>(
        input: &'src str,
        features: &UnstableFeatures,
    ) -> (bool, String, Option<ParsedSource<'src>>) {
        let mut diagnostics = DiagnosticManager::new();
        let program = parse_with_diagnostics(input, features, &mut diagnostics);

        let rejected = program.is_none();
        let text = diagnostics.to_string();

        (rejected, text, program)
    }

    fn assert_formatter_matches_regular_parser(input: &str, features: &UnstableFeatures) {
        let mut regular_diagnostics = DiagnosticManager::new();
        let regular = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            input,
            features,
            &mut regular_diagnostics,
        );

        let mut formatting_diagnostics = DiagnosticManager::new();
        let formatting = parse_with_diagnostics(input, features, &mut formatting_diagnostics);

        assert_eq!(
            formatting.as_ref().map(ParsedSource::program),
            regular.as_ref(),
            "formatter and regular parsers must produce the same AST for {input:?}"
        );
        assert_eq!(
                formatting_diagnostics.error_count(),
                regular_diagnostics.error_count(),
                "formatter and regular parsers must report the same number of errors for {input:?}, \n\
                 fmt errors: \n\t '{formatting_diagnostics}, \n regular errors: \n\t '{regular_diagnostics}"
            );
    }

    fn assert_lossless_source(input: &str, parsed: &ParsedSource<'_>) {
        let prefix = parsed.prefix();
        assert_eq!(prefix.file_id, MAIN_MODULE);

        let mut reconstructed = prefix
            .to_slice(input)
            .expect("the directive prefix must be a valid source slice")
            .to_owned();
        let mut cursor = prefix.end;

        for (_, span) in parsed.tokens() {
            assert_eq!(span.file_id, MAIN_MODULE);
            assert!(
                span.start >= prefix.end,
                "formatter tokens must not overlap the preserved directive prefix"
            );
            assert_eq!(
                span.start, cursor,
                "formatter token spans must be contiguous and in source order"
            );

            let text = span
                .to_slice(input)
                .expect("formatter token spans must be valid source slices");
            assert!(
                !text.is_empty(),
                "the formatter token stream must not contain empty source slices"
            );
            reconstructed.push_str(text);
            cursor = span.end;
        }

        assert_eq!(cursor, input.len(), "formatter tokens must reach EOF");
        assert_eq!(reconstructed, input, "formatter input must be lossless");
    }

    #[test]
    fn test_double_colon() {
        let input = "fn main() { let ab: u8 = <(u4, u4)> : :into((0b1011, 0b1101)); }";

        let (rejected, text) = parse_with(input, &UnstableFeatures::all());

        assert!(rejected);
        assert!(text.contains("Expected '::', found ':'"));
    }

    #[test]
    fn test_double_double_colon() {
        let input = "fn main() { let pk: Pubkey = witnes::::PK; }";

        let (rejected, text) = parse_with(input, &UnstableFeatures::all());

        assert!(rejected);
        assert!(
            text.contains("Expected identifier, found ::"),
            "the second :: should be reported as the error site"
        );
    }

    #[test]
    fn inverted_empty_span_from_token_gap_does_not_panic() {
        // Fuzz-found (compile_text).
        //
        // The input is irreducible. The broken `fn` prefix forces the parser into delimiter recovery.
        // The only path that requests an empty span at a lex-error gap and the
        // NUL after `enum` creates that gap.
        // Chumsky builds such spans as `next_token.start .. previous_token.end`, which is inverted
        // across the gap and panicked the strict `Span` constructor.
        //
        // Simplifying any part (even NUL to a space) loses the crash.
        let src = "fn`u({?\u{12}$0;;enum\0===lHf\u{15}";
        let (rejected, text) = parse_with(src, &UnstableFeatures::all());

        assert!(rejected, "garbage input must be rejected");
        assert!(!text.is_empty());
    }

    #[test]
    fn recovery_synchronizes_at_enum_declaration() {
        // Discriminating setup: an invalid prefix followed by a malformed
        // enum. Without `Token::Enum` in the synchronization set the whole
        // enum is swallowed into the prefix's recovery span and only one
        // error is reported; with it, the enum parses as its own item and
        // its malformation is reported as a second error.

        let src = "let invalid = 1;\nenum Action { A B }\nfn main() {}";
        let (rejected, diagnostics) = parse_with_diagnosis(src, &UnstableFeatures::all());

        assert!(rejected, "the invalid program must be rejected");
        assert_eq!(
            2,
            diagnostics.error_count(),
            "the invalid prefix and the malformed enum must each report an error"
        );
    }

    #[test]
    fn recovery_after_malformed_enum_reaches_next_item() {
        let src = "enum Action { A B }\nfn main() {}";
        let (rejected, _text) = parse_with(src, &UnstableFeatures::all());
        assert!(rejected, "a malformed enum must fail compilation");
    }

    #[test]
    fn malformed_construct_containing_enum_keyword_reports_errors() {
        // `enum` inside a badly malformed nested construct may be mistaken
        // for an item boundary; compilation must still fail cleanly.
        let src = "fn broken() { let x = (enum; }\nfn main() {}";
        let (rejected, _text) = parse_with(src, &UnstableFeatures::all());
        assert!(rejected, "a malformed construct must fail compilation");
    }

    #[test]
    fn test_gated_syntax_is_rejected_without_features() {
        // Real `use`/`mod` syntax: rejected under none() (naming the feature + a
        // -Z hint), accepted under all(). Delete when `imports` stabilizes.
        for input in [
            "use crate::foo::bar;\nfn main() { }",
            "mod inner { }\nfn main() { }",
        ] {
            let (rejected, error) = parse_with(input, &UnstableFeatures::none());
            assert!(
                rejected,
                "gated syntax must be rejected without features (if this feature was \
                 just stabilized, delete this test):\n{input}"
            );
            assert!(
                error.contains("imports") && error.contains("-Z"),
                "rejection should name the feature and suggest -Z, got:\n{error}"
            );

            let (rejected, error) = parse_with(input, &UnstableFeatures::all());
            assert!(
                !rejected,
                "the same syntax must parse with all features enabled:\n{error}"
            );
        }
    }

    #[test]
    fn test_type_heavy_program_needs_no_features() {
        // Types are traversed by `RequireFeature` but not gated, so a type-heavy,
        // import-free program must parse with no features (no false-positive gates).
        let input = r#"type Alias = u32;
fn pick(e: Either<u32, u32>) -> u32 {
    match e {
        Left(a: u32) => a,
        Right(b: u32) => b,
    }
}
fn main() {
    let casted: u32 = <(u16, u16)>::into((0xbeef, 0xbabe));
    let chosen: Alias = pick(Left(casted));
    assert!(jet::eq_32(chosen, chosen));
}
"#;
        // `parse_from_str_with_errors` returns `Some` only when no errors were
        // collected, so a non-rejection already proves there were no gate errors.
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(
            !rejected,
            "type-heavy but import-free program should parse with no features:\n{error}"
        );
    }

    #[test]
    fn test_syntax_error_does_not_produce_spurious_feature_gate_error() {
        // The gate check skips error-recovered ASTs, so a program with
        // both a syntax error and gated syntax reports only the syntax error.
        let input = "use crate::foo;\nfn main( {";
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(rejected, "broken program must be rejected");
        assert!(
            !error.contains("-Z"),
            "syntax error should not produce a spurious feature-gate hint, got:\n{error}"
        );
    }

    #[test]
    fn test_lexer_error_does_not_produce_spurious_feature_gate_error() {
        // Lexer-side companion to the case above: the stray `@` lexes with an
        // error but recovers a cleanly-parsing `use` AST, and a program that
        // didn't lex cleanly skips the gate check — so no spurious `-Z` hint.
        let input = "use crate@::foo;\nfn main() { }";
        let (rejected, error) = parse_with(input, &UnstableFeatures::none());
        assert!(rejected, "program with a lexer error must be rejected");
        assert!(
            !error.contains("-Z"),
            "lexer error should not produce a spurious feature-gate hint, got:\n{error}"
        );
    }

    #[test]
    fn test_use_decl_display_round_trips_with_aliases() {
        for input in [
            "use lib::A::foo;",
            "use lib::A::foo as bar;",
            "use lib::A::{foo, bar as baz};",
        ] {
            let (rejected, _, program) = parse_with_extended_out(input, &UnstableFeatures::all());
            assert!(!rejected, "parsing works");
            assert_eq!(program.unwrap().program().to_string(), format!("{input}\n"));
        }
    }

    #[test]
    fn statement_spans_exclude_terminating_semicolons() {
        let input = "fn main() { let value: u8 = 0; value; }";

        let (rejected, _, program) = parse_with_extended_out(input, &UnstableFeatures::none());
        assert!(!rejected, "parsing works");
        let program = program.unwrap().program().clone();

        let Item::Function(function) = &program.items()[0] else {
            panic!("expected a function item");
        };
        let ExpressionInner::Block(statements, None) = function.body().inner() else {
            panic!("expected a block containing only statements");
        };

        assert_eq!(
            statements[0].span().to_slice(input),
            Some("let value: u8 = 0")
        );
        assert_eq!(statements[1].span().to_slice(input), Some("value"));
    }

    fn parse_item(input: &str) -> Item {
        let (rejected, _, program) = parse_with_extended_out(input, &UnstableFeatures::all());
        assert!(!rejected, "parsing works");
        let program = program.unwrap().program().clone();

        program.items().first().expect("expected one item").clone()
    }

    #[test]
    fn test_enum_declaration_basic() {
        let item = parse_item("enum Path { Inherit, ColdSpend, RefreshSpend, }");
        let Item::EnumDeclaration(decl) = item else {
            panic!("expected EnumDeclaration, got {item:?}");
        };
        assert_eq!(decl.name(), "Path");
        assert_eq!(decl.variants().len(), 3);
        assert_eq!(decl.variants()[0].name(), "Inherit");
        assert_eq!(decl.variants()[2].name(), "RefreshSpend");
    }

    #[test]
    fn test_enum_declaration_pub() {
        let item = parse_item("pub enum Color { Red, Green, Blue, }");
        let Item::EnumDeclaration(decl) = item else {
            panic!("expected EnumDeclaration");
        };
        assert_eq!(decl.visibility(), &Visibility::Public);
        assert_eq!(decl.name(), "Color");
    }

    #[test]
    fn test_enum_declaration_display_round_trip() {
        let input = "enum Path { Inherit, ColdSpend, RefreshSpend, }";
        let item = parse_item(input);
        let Item::EnumDeclaration(decl) = item else {
            panic!("expected EnumDeclaration");
        };
        assert_eq!(
            decl.to_string(),
            "enum Path { Inherit, ColdSpend, RefreshSpend, }"
        );
    }

    #[test]
    fn test_enum_declaration_reserved_name() {
        for reserved in RESERVED_PATTERN_NAMES {
            let input = format!("enum {reserved} {{ A, B, }}");
            let (rejected, error) = parse_with(&input, &UnstableFeatures::none());
            assert!(rejected, "enum name {reserved} is reserved");
            assert!(
                error.contains("reserved"),
                "error should say the name is reserved: {error}"
            );
        }
    }

    #[test]
    fn formatting_parse_is_lossless_after_directive_prescan() {
        let input = "// header\r\nsimc \"*\";\r\n\t/* block */ fn main() { // body\r\n\t}\r";

        let (_rejected, _error, parsed) = parse_with_extended_out(input, &UnstableFeatures::none());
        let parsed = parsed.expect("formatting parse should succeed");

        assert_eq!(
            parsed.prefix().to_slice(input),
            Some("// header\r\nsimc \"*\";")
        );
        for trivia in [
            crate::lexer::TriviaKind::BlockComment,
            crate::lexer::TriviaKind::LineComment,
            crate::lexer::TriviaKind::Newline,
            crate::lexer::TriviaKind::Whitespace,
        ] {
            assert!(
                    parsed.tokens().iter().any(
                        |(token, _)| matches!(token, crate::lexer::FmtToken::Trivia(token_trivia) if token_trivia.kind() == trivia)
                    ),
                    "formatter token stream should retain {trivia:?}"
                );
        }
        assert_lossless_source(input, &parsed);
        assert_eq!(parsed.program().items().len(), 1);
    }

    #[test]
    fn formatting_parse_matches_regular_parser_pipeline() {
        let no_features = UnstableFeatures::none();
        let all_features = UnstableFeatures::all();

        for (input, features) in [
            (
                "/* header */\r\nfn\tmain() { // comment\r\n}\r",
                &no_features,
            ),
            ("// version\r\nsimc \"*\";\r\nfn main() {}", &no_features),
            ("use crate::foo::bar;\nfn main() {}", &no_features),
            ("use crate::foo::bar;\nfn main() {}", &all_features),
            ("fn main( {", &no_features),
            ("fn main() { @// comment }", &no_features),
        ] {
            assert_formatter_matches_regular_parser(input, features);
        }
    }

    #[test]
    fn formatting_parse_ignores_preexisting_errors() {
        let input = "fn main() {}";
        let mut diagnostics = DiagnosticManager::new();
        diagnostics.push(Diagnostic::global(Error::CannotParse {
            msg: "an error from an earlier source file".to_owned(),
        }));
        let before = diagnostics.error_count();

        let parsed = parse_with_diagnostics(input, &UnstableFeatures::none(), &mut diagnostics);

        assert!(
            parsed.is_some(),
            "valid source must still produce ParsedSource"
        );
        assert_eq!(diagnostics.error_count(), before);
        assert_eq!(diagnostics.diagnostics().len(), before);
    }

    #[test]
    fn formatting_parse_stops_after_invalid_directive() {
        for (input, is_malformed) in [
            ("simc \"*\"\nfn broken( @", true),
            ("simc \">99.0.0\"; @", false),
        ] {
            let (rejected, diagnostics) = parse_with_diagnosis(input, &UnstableFeatures::none());

            assert!(rejected, "invalid directive must abort formatting parse");
            assert_eq!(
                diagnostics.error_count(),
                1,
                "the invalid body must not add diagnostics after prescan aborts"
            );
            if is_malformed {
                assert!(matches!(
                    diagnostics.diagnostics()[0].error(),
                    Error::MalformedSimcDirective
                ));
            } else {
                assert!(matches!(
                    diagnostics.diagnostics()[0].error(),
                    Error::SimcVersionMismatch { .. }
                ));
            }
        }
    }

    #[test]
    fn formatting_parse_reports_missing_match_arm_comma() {
        let input = "fn main() { match true { false => () true => (), } }";

        let (rejected, error) = parse_with(input, &UnstableFeatures::none());

        assert!(rejected);
        assert!(
            error.contains("Missing ',' after a match arm that isn't block expression"),
            "expected the missing-comma diagnostic, got {error:?}"
        );
    }
}
