//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::fmt;
use std::num::NonZeroUsize;
use std::str::FromStr;
use std::sync::Arc;

use either::Either;
use itertools::Itertools;
use miniscript::iter::{Tree, TreeLike};
use pest::Parser;
use pest_derive::Parser;
use simplicity::elements::hex::FromHex;

use crate::error::{Error, RichError, WithFile, WithSpan};
use crate::num::NonZeroPow2Usize;
use crate::pattern::Pattern;
use crate::types::{AliasedType, BuiltinAlias, TypeConstructible, UIntType};

#[derive(Parser)]
#[grammar = "minimal.pest"]
pub struct IdentParser;

/// Position of an object inside a file.
///
/// [`pest::Position<'i>`] forces us to track lifetimes, so we introduce our own struct.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Position {
    /// Line where the object is located.
    ///
    /// Starts at 1.
    pub line: NonZeroUsize,
    /// Column where the object is located.
    ///
    /// Starts at 1.
    pub col: NonZeroUsize,
}

impl Position {
    /// Create a new position.
    ///
    /// ## Panics
    ///
    /// Line or column are zero.
    pub fn new(line: usize, col: usize) -> Self {
        let line = NonZeroUsize::new(line).expect("PEST lines start at 1");
        let col = NonZeroUsize::new(col).expect("PEST columns start at 1");
        Self { line, col }
    }
}

/// Area that an object spans inside a file.
///
/// The area cannot be empty.
///
/// [`pest::Span<'i>`] forces us to track lifetimes, so we introduce our own struct.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// Position where the object starts, inclusively.
    pub start: Position,
    /// Position where the object ends, inclusively.
    pub end: Position,
}

impl Span {
    /// Create a new span.
    ///
    /// ## Panics
    ///
    /// Start comes after end.
    pub fn new(start: Position, end: Position) -> Self {
        assert!(start.line <= end.line, "Start cannot come after end");
        assert!(
            start.line < end.line || start.col <= end.col,
            "Start cannot come after end"
        );
        Self { start, end }
    }

    /// Check if the span covers more than one line.
    pub fn is_multiline(&self) -> bool {
        self.start.line < self.end.line
    }
}

impl<'a> From<&'a pest::iterators::Pair<'_, Rule>> for Span {
    fn from(pair: &'a pest::iterators::Pair<Rule>) -> Self {
        let (line, col) = pair.line_col();
        let start = Position::new(line, col);
        // end_pos().line_col() is O(n) in file length
        // https://github.com/pest-parser/pest/issues/560
        // We should generate `Span`s only on error paths
        let (line, col) = pair.as_span().end_pos().line_col();
        let end = Position::new(line, col);
        Self::new(start, end)
    }
}

impl<'a> From<&'a str> for Span {
    fn from(s: &str) -> Self {
        let start = Position::new(1, 1);
        let end_line = std::cmp::max(1, s.lines().count());
        let end_col = std::cmp::max(1, s.lines().next_back().unwrap_or("").len());
        let end = Position::new(end_line, end_col);
        debug_assert!(start.line <= end.line);
        debug_assert!(start.line < end.line || start.col <= end.col);
        Span::new(start, end)
    }
}

/// Implementations for newtypes that wrap [`Arc<str>`].
macro_rules! wrapped_string {
    ($wrapper:ident) => {
        impl $wrapper {
            /// Access the inner string.
            pub fn as_inner(&self) -> &str {
                self.0.as_ref()
            }

            /// Create a wrapped string without checking for validity.
            #[cfg(test)]
            pub fn from_str_unchecked(s: &str) -> Self {
                Self(std::sync::Arc::from(s))
            }
        }

        impl std::fmt::Display for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }

        impl std::fmt::Debug for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

/// A program is a sequence of items.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Program {
    items: Arc<[Item]>,
    span: Span,
}

impl Program {
    /// Access the items of the program.
    pub fn items(&self) -> &[Item] {
        &self.items
    }
}

/// An item is a component of a program.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Item {
    /// A type alias.
    TypeAlias(TypeAlias),
    /// A function.
    Function(Function),
}

/// Definition of a function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Function {
    name: FunctionName,
    params: Arc<[FunctionParam]>,
    ret: Option<AliasedType>,
    body: Expression,
    span: Span,
}

impl Function {
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
}

/// Parameter of a function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionParam {
    identifier: Identifier,
    ty: AliasedType,
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
}

/// Name of a function.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionName(Arc<str>);

wrapped_string!(FunctionName);

impl FunctionName {
    /// Return the name of the main function.
    pub fn main() -> Self {
        Self(Arc::from("main"))
    }
}

/// A statement is a component of a block expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// An expression that returns nothing (the unit value).
    Expression(Expression),
}

/// Identifier of a variable.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Identifier(Arc<str>);

wrapped_string!(Identifier);

/// The output of an expression is assigned to a pattern.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Assignment {
    /// The pattern.
    pub pattern: Pattern,
    /// The return type of the expression.
    pub ty: AliasedType,
    /// The expression.
    pub expression: Expression,
    /// Area that this assignment spans in the source file.
    pub span: Span,
}

/// Call expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Call {
    /// The name of the call.
    pub name: CallName,
    /// The arguments to the call.
    pub args: Arc<[Expression]>,
    /// Area that this call spans in the source file.
    pub span: Span,
}

/// Name of a call.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CallName {
    /// Name of a jet.
    Jet(JetName),
    /// Left unwrap function.
    UnwrapLeft(AliasedType),
    /// Right unwrap function.
    UnwrapRight(AliasedType),
    /// Some unwrap function.
    Unwrap,
    /// Cast from the given source type.
    TypeCast(AliasedType),
    /// Name of a custom function.
    Custom(FunctionName),
}

/// Name of a jet.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct JetName(Arc<str>);

wrapped_string!(JetName);

/// A type alias.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeAlias {
    /// Name of the alias.
    pub name: Identifier,
    /// Type that the alias resolves to.
    ///
    /// During the parsing stage, these types may include aliases.
    /// The compiler checks if all contained aliases have been declared before.
    pub ty: AliasedType,
    /// Area that the alias spans in the source file.
    pub span: Span,
}

/// An expression is something that returns a value.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Expression {
    /// The kind of expression
    pub inner: ExpressionInner,
    /// Area that this expression spans in the source file.
    pub span: Span,
}

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

/// A single expression directly returns a value.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct SingleExpression {
    /// The kind of single expression
    pub inner: SingleExpressionInner,
    /// Area that this expression spans in the source file.
    pub span: Span,
}

/// The kind of single expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SingleExpressionInner {
    /// Either wrapper expression
    Either(Either<Arc<Expression>, Arc<Expression>>),
    /// Option wrapper expression
    Option(Option<Arc<Expression>>),
    /// Boolean literal expression
    Boolean(bool),
    /// Unsigned integer literal in decimal representation
    Decimal(UnsignedDecimal),
    /// Unsigned integer literal in bit string representation
    BitString(Bits),
    /// Unsigned integer literal in byte string representation
    ByteString(Bytes),
    /// Witness identifier expression
    Witness(WitnessName),
    /// Variable identifier expression
    Variable(Identifier),
    /// Function call
    Call(Call),
    /// Expression in parentheses
    Expression(Arc<Expression>),
    /// Match expression over a sum type
    Match(Match),
    /// Tuple wrapper expression
    Tuple(Arc<[Expression]>),
    /// Array wrapper expression
    Array(Arc<[Expression]>),
    /// List wrapper expression
    ///
    /// The exclusive upper bound on the list size is not known at this point
    List(Arc<[Expression]>),
}

/// Valid unsigned decimal string.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct UnsignedDecimal(Arc<str>);

wrapped_string!(UnsignedDecimal);

/// Bit string whose length is a power of two.
///
/// There is at least 1 bit.
/// There are at most 256 bits.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Bits(BitsInner);

/// Private enum that upholds invariants about its values.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum BitsInner {
    /// Least significant bit of byte.
    ///
    /// The bit is saved as a [`u8`] value that is always less than or equal to 1.
    U1(u8),
    /// Two least significant bits of byte.
    ///
    /// The bits are saved as a [`u8`] value that is always less than or equal to 3.
    U2(u8),
    /// Four least significant bits of byte.
    ///
    /// The bits are saved as a [`u8`] value that is always less than or equal to 15.
    U4(u8),
    /// All bits from byte string.
    ///
    /// There are at least 8 bits, aka 1 byte.
    /// There are at most 256 bits, aka 32 bytes.
    Long(Arc<[u8]>),
}

impl Bits {
    /// Access the contained 1-bit value,
    /// represented by a [`u8`] integer that is always less than or equal to 1.
    pub fn as_u1(&self) -> Option<u8> {
        match self.0 {
            BitsInner::U1(byte) => {
                debug_assert!(byte <= 1);
                Some(byte)
            }
            _ => None,
        }
    }

    /// Access the contained 2-bit value,
    /// represented by a [`u8`] integer that is always less than or equal to 3.
    pub fn as_u2(&self) -> Option<u8> {
        match self.0 {
            BitsInner::U2(byte) => {
                debug_assert!(byte <= 3);
                Some(byte)
            }
            _ => None,
        }
    }

    /// Access the contained 4-bit value,
    /// represented by a [`u8`] integer that is always less than or equal to 15.
    pub fn as_u4(&self) -> Option<u8> {
        match self.0 {
            BitsInner::U4(byte) => {
                debug_assert!(byte <= 15);
                Some(byte)
            }
            _ => None,
        }
    }

    /// Access the contained value that is between 8 and 256 bits long,
    /// represented by a slice that is between 1 and 32 bytes long.
    pub fn as_long(&self) -> Option<&[u8]> {
        match &self.0 {
            BitsInner::Long(bytes) => {
                debug_assert!(1 <= bytes.len());
                debug_assert!(bytes.len() <= 32);
                Some(bytes.as_ref())
            }
            _ => None,
        }
    }
}

/// Byte string whose length is a power of two.
///
/// There is at least 1 byte.
/// There are at most 32 bytes.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Bytes(Arc<[u8]>);

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// String that is a witness name.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct WitnessName(Arc<str>);

wrapped_string!(WitnessName);

/// Match expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Match {
    /// Expression whose output is matched.
    scrutinee: Arc<Expression>,
    /// Match arm for left sum values.
    left: MatchArm,
    /// Match arm for right sum values.
    right: MatchArm,
    /// Area that the match spans in the source file.
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

/// Arm of a match expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MatchArm {
    /// Matched pattern
    pub pattern: MatchPattern,
    /// Executed expression
    pub expression: Arc<Expression>,
}

/// Pattern of a match arm.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum MatchPattern {
    /// Bind inner value of left value to variable name.
    Left(Identifier, AliasedType),
    /// Bind inner value of right value to variable name.
    Right(Identifier, AliasedType),
    /// Match none value (no binding).
    None,
    /// Bind inner value of some value to variable name.
    Some(Identifier, AliasedType),
    /// Match false value (no binding).
    False,
    /// Match true value (no binding).
    True,
}

impl MatchPattern {
    /// Access the identifier of a pattern that binds a variable.
    pub fn as_variable(&self) -> Option<&Identifier> {
        match self {
            MatchPattern::Left(i, _) | MatchPattern::Right(i, _) | MatchPattern::Some(i, _) => {
                Some(i)
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }

    /// Access the identifier and the type of a pattern that binds a variable.
    pub fn as_typed_variable(&self) -> Option<(&Identifier, &AliasedType)> {
        match self {
            MatchPattern::Left(i, ty) | MatchPattern::Right(i, ty) | MatchPattern::Some(i, ty) => {
                Some((i, ty))
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }
}

impl fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchPattern::Left(i, ty) => write!(f, "Left({i}: {ty}"),
            MatchPattern::Right(i, ty) => write!(f, "Right({i}: {ty}"),
            MatchPattern::None => write!(f, "None"),
            MatchPattern::Some(i, ty) => write!(f, "Some({i}: {ty}"),
            MatchPattern::False => write!(f, "false"),
            MatchPattern::True => write!(f, "true"),
        }
    }
}

/// Trait for types that can be parsed from a PEST pair.
trait PestParse: Sized {
    /// Expected rule for parsing the type.
    const RULE: Rule;

    /// Parse a value of the type from a PEST pair.
    ///
    /// # Panics
    ///
    /// The rule of the pair is not the expected rule ([`Self::RULE`]).
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError>;
}

/// Copy of [`FromStr`] that internally uses the PEST parser.
pub trait ParseFromStr: Sized {
    /// Parse a value from the string `s`.
    fn parse_from_str(s: &str) -> Result<Self, RichError>;
}

impl<A: PestParse> ParseFromStr for A {
    fn parse_from_str(s: &str) -> Result<Self, RichError> {
        let mut pairs = IdentParser::parse(A::RULE, s)
            .map_err(RichError::from)
            .with_file(s)?;
        let pair = pairs.next().unwrap();
        A::parse(pair).with_file(s)
    }
}

impl PestParse for Program {
    const RULE: Rule = Rule::program;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let span = Span::from(&pair);
        let items = pair
            .into_inner()
            .filter_map(|pair| match pair.as_rule() {
                Rule::item => Some(Item::parse(pair)),
                Rule::EOI => None,
                _ => unreachable!("Corrupt grammar"),
            })
            .collect::<Result<Arc<[Item]>, RichError>>()?;
        Ok(Program { items, span })
    }
}

impl PestParse for Item {
    const RULE: Rule = Rule::item;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::type_alias => TypeAlias::parse(pair).map(Item::TypeAlias),
            Rule::function => Function::parse(pair).map(Item::Function),
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

impl PestParse for Function {
    const RULE: Rule = Rule::function;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let span = Span::from(&pair);
        let mut it = pair.into_inner();
        let name = FunctionName::parse(it.next().unwrap())?;
        let params = {
            let pair = it.next().unwrap();
            debug_assert!(matches!(pair.as_rule(), Rule::function_params));
            pair.into_inner()
                .map(FunctionParam::parse)
                .collect::<Result<Arc<[FunctionParam]>, RichError>>()?
        };
        let ret = match it.peek().unwrap().as_rule() {
            Rule::function_return => {
                let pair = it.next().unwrap();
                debug_assert!(matches!(pair.as_rule(), Rule::function_return));
                let pair = pair.into_inner().next().unwrap();
                let ty = AliasedType::parse(pair)?;
                Some(ty)
            }
            _ => None,
        };
        let body = Expression::parse(it.next().unwrap())?;

        Ok(Self {
            name,
            params,
            ret,
            body,
            span,
        })
    }
}

impl PestParse for FunctionName {
    const RULE: Rule = Rule::function_name;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let name = Arc::from(pair.as_str());
        Ok(Self(name))
    }
}

impl PestParse for FunctionParam {
    const RULE: Rule = Rule::typed_identifier;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let mut it = pair.into_inner();
        let identifier = Identifier::parse(it.next().unwrap())?;
        let ty = AliasedType::parse(it.next().unwrap())?;
        Ok(Self { identifier, ty })
    }
}

impl PestParse for Statement {
    const RULE: Rule = Rule::statement;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let inner_pair = pair.into_inner().next().unwrap();
        match inner_pair.as_rule() {
            Rule::assignment => Assignment::parse(inner_pair).map(Statement::Assignment),
            Rule::expression => Expression::parse(inner_pair).map(Statement::Expression),
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

impl PestParse for Pattern {
    const RULE: Rule = Rule::pattern;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let pair = PatternPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::pattern => {}
                Rule::variable_pattern => {
                    let identifier = Identifier::parse(data.node.0.into_inner().next().unwrap())?;
                    output.push(Pattern::Identifier(identifier));
                }
                Rule::ignore_pattern => {
                    output.push(Pattern::Ignore);
                }
                Rule::tuple_pattern => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Pattern::tuple(elements));
                }
                Rule::array_pattern => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Pattern::array(elements));
                }
                _ => unreachable!("Corrupt grammar"),
            }
        }

        debug_assert!(output.len() == 1);
        Ok(output.pop().unwrap())
    }
}

impl PestParse for Identifier {
    const RULE: Rule = Rule::identifier;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let identifier = Arc::from(pair.as_str());
        Ok(Identifier(identifier))
    }
}

impl PestParse for Assignment {
    const RULE: Rule = Rule::assignment;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let span = Span::from(&pair);
        let mut inner_pair = pair.into_inner();
        let pattern = Pattern::parse(inner_pair.next().unwrap())?;
        let ty = AliasedType::parse(inner_pair.next().unwrap())?;
        let expression = Expression::parse(inner_pair.next().unwrap())?;
        Ok(Assignment {
            pattern,
            ty,
            expression,
            span,
        })
    }
}

impl PestParse for Call {
    const RULE: Rule = Rule::call_expr;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let span = Span::from(&pair);
        let mut it = pair.into_inner();
        let name = CallName::parse(it.next().unwrap())?;
        let args = {
            let pair = it.next().unwrap();
            debug_assert!(matches!(pair.as_rule(), Rule::call_args));
            pair.into_inner()
                .map(Expression::parse)
                .collect::<Result<Arc<[Expression]>, RichError>>()?
        };

        Ok(Self { name, args, span })
    }
}

impl PestParse for CallName {
    const RULE: Rule = Rule::call_name;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::jet => JetName::parse(pair).map(Self::Jet),
            Rule::unwrap_left => {
                let inner = pair.into_inner().next().unwrap();
                AliasedType::parse(inner).map(Self::UnwrapLeft)
            }
            Rule::unwrap_right => {
                let inner = pair.into_inner().next().unwrap();
                AliasedType::parse(inner).map(Self::UnwrapRight)
            }
            Rule::unwrap => Ok(Self::Unwrap),
            Rule::type_cast => {
                let inner = pair.into_inner().next().unwrap();
                AliasedType::parse(inner).map(Self::TypeCast)
            }
            Rule::function_name => FunctionName::parse(pair).map(Self::Custom),
            _ => panic!("Corrupt grammar"),
        }
    }
}

impl PestParse for JetName {
    const RULE: Rule = Rule::jet;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let jet_name = pair.as_str().strip_prefix("jet_").unwrap();
        Ok(Self(Arc::from(jet_name)))
    }
}

impl PestParse for TypeAlias {
    const RULE: Rule = Rule::type_alias;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let span = Span::from(&pair);
        let mut it = pair.into_inner();
        let name = Identifier::parse(it.next().unwrap())?;
        let ty = AliasedType::parse(it.next().unwrap())?;
        Ok(Self { name, ty, span })
    }
}

impl PestParse for Expression {
    const RULE: Rule = Rule::expression;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        let span = Span::from(&pair);
        let pair = match pair.as_rule() {
            Rule::expression => pair.into_inner().next().unwrap(),
            Rule::block_expression | Rule::single_expression => pair,
            _ => unreachable!("Corrupt grammar"),
        };

        let inner = match pair.as_rule() {
            Rule::block_expression => {
                let mut it = pair.into_inner().peekable();
                let statements = it
                    .peeking_take_while(|pair| matches!(pair.as_rule(), Rule::statement))
                    .map(Statement::parse)
                    .collect::<Result<Arc<[Statement]>, RichError>>()?;
                let expression = it
                    .next()
                    .map(|pair| Expression::parse(pair).map(Arc::new))
                    .transpose()?;
                ExpressionInner::Block(statements, expression)
            }
            Rule::single_expression => ExpressionInner::Single(SingleExpression::parse(pair)?),
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(Expression { inner, span })
    }
}

impl PestParse for SingleExpression {
    const RULE: Rule = Rule::single_expression;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));

        let span = Span::from(&pair);
        let inner_pair = pair.into_inner().next().unwrap();

        let inner = match inner_pair.as_rule() {
            Rule::left_expr => {
                let l = inner_pair.into_inner().next().unwrap();
                Expression::parse(l)
                    .map(Arc::new)
                    .map(Either::Left)
                    .map(SingleExpressionInner::Either)?
            }
            Rule::right_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                Expression::parse(r)
                    .map(Arc::new)
                    .map(Either::Right)
                    .map(SingleExpressionInner::Either)?
            }
            Rule::none_expr => SingleExpressionInner::Option(None),
            Rule::some_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                Expression::parse(r)
                    .map(Arc::new)
                    .map(Some)
                    .map(SingleExpressionInner::Option)?
            }
            Rule::false_expr => SingleExpressionInner::Boolean(false),
            Rule::true_expr => SingleExpressionInner::Boolean(true),
            Rule::call_expr => SingleExpressionInner::Call(Call::parse(inner_pair)?),
            Rule::bit_string => Bits::parse(inner_pair).map(SingleExpressionInner::BitString)?,
            Rule::byte_string => Bytes::parse(inner_pair).map(SingleExpressionInner::ByteString)?,
            Rule::unsigned_decimal => {
                UnsignedDecimal::parse(inner_pair).map(SingleExpressionInner::Decimal)?
            }
            Rule::witness_expr => {
                let witness_pair = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Witness(WitnessName::parse(witness_pair)?)
            }
            Rule::variable_expr => {
                let identifier_pair = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Variable(Identifier::parse(identifier_pair)?)
            }
            Rule::expression => {
                SingleExpressionInner::Expression(Expression::parse(inner_pair).map(Arc::new)?)
            }
            Rule::match_expr => Match::parse(inner_pair).map(SingleExpressionInner::Match)?,
            Rule::tuple_expr => inner_pair
                .clone()
                .into_inner()
                .map(Expression::parse)
                .collect::<Result<Arc<[Expression]>, _>>()
                .map(SingleExpressionInner::Tuple)?,
            Rule::array_expr => inner_pair
                .clone()
                .into_inner()
                .map(Expression::parse)
                .collect::<Result<Arc<[Expression]>, _>>()
                .map(SingleExpressionInner::Array)?,
            Rule::list_expr => {
                let elements = inner_pair
                    .into_inner()
                    .map(|inner| Expression::parse(inner))
                    .collect::<Result<Arc<_>, _>>()?;
                SingleExpressionInner::List(elements)
            }
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(SingleExpression { inner, span })
    }
}

impl PestParse for UnsignedDecimal {
    const RULE: Rule = Rule::unsigned_decimal;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let decimal = Arc::from(pair.as_str().replace('_', ""));
        Ok(Self(decimal))
    }
}

impl PestParse for Bits {
    const RULE: Rule = Rule::bit_string;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let bit_string = pair.as_str();
        debug_assert!(&bit_string[0..2] == "0b");

        let bits = &bit_string[2..];
        if !bits.len().is_power_of_two() {
            return Err(Error::BitStringPow2(bits.len())).with_span(&pair);
        }

        let byte_len = (bits.len() + 7) / 8;
        let mut bytes = Vec::with_capacity(byte_len);
        let padding_len = 8usize.saturating_sub(bits.len());
        let padding = std::iter::repeat('0').take(padding_len);
        let mut padded_bits = padding.chain(bits.chars());

        for _ in 0..byte_len {
            let mut byte = 0u8;
            for _ in 0..8 {
                let bit = padded_bits.next().unwrap();
                byte = byte << 1 | if bit == '1' { 1 } else { 0 };
            }
            bytes.push(byte);
        }

        match bits.len() {
            1 => {
                debug_assert!(bytes[0] < 2);
                Ok(Bits(BitsInner::U1(bytes[0])))
            }
            2 => {
                debug_assert!(bytes[0] < 4);
                Ok(Bits(BitsInner::U2(bytes[0])))
            }
            4 => {
                debug_assert!(bytes[0] < 16);
                Ok(Bits(BitsInner::U4(bytes[0])))
            }
            8 | 16 | 32 | 64 | 128 | 256 => Ok(Bits(BitsInner::Long(bytes.into_iter().collect()))),
            n => Err(Error::BitStringPow2(n)).with_span(&pair),
        }
    }
}

impl PestParse for Bytes {
    const RULE: Rule = Rule::byte_string;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let hex_string = pair.as_str();

        let hex_digits = hex_string
            .strip_prefix("0x")
            .expect("Grammar enforces prefix")
            .replace('_', "");
        if hex_digits.len() < 2 || 64 < hex_digits.len() || !hex_digits.len().is_power_of_two() {
            return Err(Error::HexStringPow2(hex_digits.len())).with_span(&pair);
        }

        Vec::<u8>::from_hex(&hex_digits)
            .map_err(Error::from)
            .with_span(&pair)
            .map(Arc::from)
            .map(Bytes)
    }
}

impl PestParse for WitnessName {
    const RULE: Rule = Rule::witness_name;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let name = Arc::from(pair.as_str());
        Ok(Self(name))
    }
}

impl PestParse for Match {
    const RULE: Rule = Rule::match_expr;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let span = Span::from(&pair);
        let mut it = pair.into_inner();
        let scrutinee_pair = it.next().unwrap();
        let scrutinee = Expression::parse(scrutinee_pair.clone()).map(Arc::new)?;
        let first = MatchArm::parse(it.next().unwrap())?;
        let second = MatchArm::parse(it.next().unwrap())?;

        let (left, right) = match (&first.pattern, &second.pattern) {
            (MatchPattern::Left(..), MatchPattern::Right(..)) => (first, second),
            (MatchPattern::Right(..), MatchPattern::Left(..)) => (second, first),
            (MatchPattern::None, MatchPattern::Some(..)) => (first, second),
            (MatchPattern::False, MatchPattern::True) => (first, second),
            (MatchPattern::Some(..), MatchPattern::None) => (second, first),
            (MatchPattern::True, MatchPattern::False) => (second, first),
            (p1, p2) => {
                return Err(Error::IncompatibleMatchArms(p1.clone(), p2.clone())).with_span(span)
            }
        };

        Ok(Self {
            scrutinee,
            left,
            right,
            span,
        })
    }
}

impl PestParse for MatchArm {
    const RULE: Rule = Rule::match_arm;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let mut it = pair.into_inner();
        let pattern = MatchPattern::parse(it.next().unwrap())?;
        let expression = Expression::parse(it.next().unwrap()).map(Arc::new)?;
        Ok(MatchArm {
            pattern,
            expression,
        })
    }
}

impl PestParse for MatchPattern {
    const RULE: Rule = Rule::match_pattern;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let pair = pair.into_inner().next().unwrap();
        let ret = match pair.as_rule() {
            rule @ (Rule::left_pattern | Rule::right_pattern | Rule::some_pattern) => {
                let mut it = pair.into_inner();
                let identifier = Identifier::parse(it.next().unwrap())?;
                let ty = AliasedType::parse(it.next().unwrap())?;

                match rule {
                    Rule::left_pattern => MatchPattern::Left(identifier, ty),
                    Rule::right_pattern => MatchPattern::Right(identifier, ty),
                    Rule::some_pattern => MatchPattern::Some(identifier, ty),
                    _ => unreachable!("Covered by outer match"),
                }
            }
            Rule::none_pattern => MatchPattern::None,
            Rule::false_pattern => MatchPattern::False,
            Rule::true_pattern => MatchPattern::True,
            _ => unreachable!("Corrupt grammar"),
        };
        Ok(ret)
    }
}

impl PestParse for AliasedType {
    const RULE: Rule = Rule::ty;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        enum Item {
            Type(AliasedType),
            Size(usize),
            Bound(NonZeroPow2Usize),
        }

        impl Item {
            fn unwrap_type(self) -> AliasedType {
                match self {
                    Item::Type(ty) => ty,
                    _ => panic!("Not a type"),
                }
            }

            fn unwrap_size(self) -> usize {
                match self {
                    Item::Size(size) => size,
                    _ => panic!("Not a size"),
                }
            }

            fn unwrap_bound(self) -> NonZeroPow2Usize {
                match self {
                    Item::Bound(size) => size,
                    _ => panic!("Not a bound"),
                }
            }
        }

        assert!(matches!(pair.as_rule(), Self::RULE));
        let pair = TyPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::alias_name => {
                    let pair = data.node.0.into_inner().next().unwrap();
                    let identifier = Identifier::parse(pair)?;
                    output.push(Item::Type(AliasedType::alias(identifier)));
                }
                Rule::builtin_alias => {
                    let builtin = BuiltinAlias::parse(data.node.0)?;
                    output.push(Item::Type(AliasedType::builtin(builtin)));
                }
                Rule::unsigned_type => {
                    let uint_ty = UIntType::parse(data.node.0)?;
                    output.push(Item::Type(AliasedType::from(uint_ty)));
                }
                Rule::sum_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    let l = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(AliasedType::either(l, r)));
                }
                Rule::option_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(AliasedType::option(r)));
                }
                Rule::boolean_type => {
                    output.push(Item::Type(AliasedType::boolean()));
                }
                Rule::tuple_type => {
                    let size = data.node.n_children();
                    let elements: Vec<AliasedType> = output
                        .split_off(output.len() - size)
                        .into_iter()
                        .map(Item::unwrap_type)
                        .collect();
                    debug_assert_eq!(elements.len(), size);
                    output.push(Item::Type(AliasedType::tuple(elements)));
                }
                Rule::array_type => {
                    let size = output.pop().unwrap().unwrap_size();
                    let el = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(AliasedType::array(el, size)));
                }
                Rule::array_size => {
                    let size_str = data.node.0.as_str();
                    let size = size_str.parse::<usize>().with_span(&data.node.0)?;
                    output.push(Item::Size(size));
                }
                Rule::list_type => {
                    let bound = output.pop().unwrap().unwrap_bound();
                    let el = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(AliasedType::list(el, bound)));
                }
                Rule::list_bound => {
                    let bound_str = data.node.0.as_str();
                    let bound = bound_str.parse::<usize>().with_span(&data.node.0)?;
                    let bound = NonZeroPow2Usize::new(bound)
                        .ok_or(Error::ListBoundPow2(bound))
                        .with_span(&data.node.0)?;
                    output.push(Item::Bound(bound));
                }
                Rule::ty => {}
                _ => unreachable!("Corrupt grammar"),
            }
        }

        debug_assert!(output.len() == 1);
        Ok(output.pop().unwrap().unwrap_type())
    }
}

impl PestParse for UIntType {
    const RULE: Rule = Rule::unsigned_type;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        let ret = match pair.as_str() {
            "u1" => UIntType::U1,
            "u2" => UIntType::U2,
            "u4" => UIntType::U4,
            "u8" => UIntType::U8,
            "u16" => UIntType::U16,
            "u32" => UIntType::U32,
            "u64" => UIntType::U64,
            "u128" => UIntType::U128,
            "u256" => UIntType::U256,
            _ => unreachable!("Corrupt grammar"),
        };
        Ok(ret)
    }
}

impl PestParse for BuiltinAlias {
    const RULE: Rule = Rule::builtin_alias;

    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Self::RULE));
        Self::from_str(pair.as_str())
            .map_err(Error::CannotParse)
            .with_span(&pair)
    }
}

/// Pair of tokens from the 'pattern' rule.
#[derive(Clone, Debug)]
struct PatternPair<'a>(pest::iterators::Pair<'a, Rule>);

impl<'a> TreeLike for PatternPair<'a> {
    fn as_node(&self) -> Tree<Self> {
        let mut it = self.0.clone().into_inner();
        match self.0.as_rule() {
            Rule::variable_pattern | Rule::ignore_pattern => Tree::Nullary,
            Rule::pattern => {
                let l = it.next().unwrap();
                Tree::Unary(PatternPair(l))
            }
            Rule::tuple_pattern | Rule::array_pattern => {
                let children: Arc<[PatternPair]> = it.map(PatternPair).collect();
                Tree::Nary(children)
            }
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

/// Pair of tokens from the 'ty' rule.
#[derive(Clone, Debug)]
struct TyPair<'a>(pest::iterators::Pair<'a, Rule>);

impl<'a> TreeLike for TyPair<'a> {
    fn as_node(&self) -> Tree<Self> {
        let mut it = self.0.clone().into_inner();
        match self.0.as_rule() {
            Rule::boolean_type
            | Rule::unsigned_type
            | Rule::array_size
            | Rule::list_bound
            | Rule::alias_name
            | Rule::builtin_alias => Tree::Nullary,
            Rule::ty | Rule::option_type => {
                let l = it.next().unwrap();
                Tree::Unary(TyPair(l))
            }
            Rule::sum_type | Rule::array_type | Rule::list_type => {
                let l = it.next().unwrap();
                let r = it.next().unwrap();
                Tree::Binary(TyPair(l), TyPair(r))
            }
            Rule::tuple_type => Tree::Nary(it.map(TyPair).collect()),
            _ => unreachable!("Corrupt grammar"),
        }
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
