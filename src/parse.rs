//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::elements::hex::FromHex;
use simplicity::Value;

use crate::error::{Error, RichError, WithSpan};
use crate::num::{NonZeroPow2Usize, U256};
use crate::types::{AliasedType, TypeConstructible, UIntType};
use crate::Rule;

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
/// [`pest::Span<'i>`] forces us to track lifetimes, so we introduce our own struct.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// Position where the object starts.
    pub start: Position,
    /// Position where the object ends.
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

/// A complete simplicity program.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Program {
    /// The statements in the program.
    pub statements: Vec<Statement>,
}

/// A statement in a simplicity program.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// An expression that returns nothing (the unit value).
    Expression(Expression),
    /// A type alias.
    TypeAlias(TypeAlias),
}

/// Pattern for binding values to variables.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Pattern {
    /// Match any value and bind it to variable name.
    Identifier(Identifier),
    /// Match any value but ignore it.
    Ignore,
    /// Recursively match the components of a tuple value
    Tuple(Arc<[Self]>),
    /// Recursively match the elements of an array value.
    Array(Arc<[Self]>),
}

impl Pattern {
    /// Construct a product pattern.
    pub fn product(l: Self, r: Self) -> Self {
        Self::tuple([l, r])
    }

    /// Construct a tuple pattern.
    pub fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self::Tuple(elements.into_iter().collect())
    }

    /// Construct an array pattern.
    pub fn array<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self::Array(elements.into_iter().collect())
    }
}

impl<'a> TreeLike for &'a Pattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Pattern::Identifier(_) | Pattern::Ignore => Tree::Nullary,
            Pattern::Tuple(elements) | Pattern::Array(elements) => {
                Tree::Nary(elements.iter().collect())
            }
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Pattern::Identifier(i) => write!(f, "{i}")?,
                Pattern::Ignore => write!(f, "_")?,
                Pattern::Tuple(elements) => match data.n_children_yielded {
                    0 => {
                        f.write_str("(")?;
                        if 0 == elements.len() {
                            f.write_str(")")?;
                        }
                    }
                    n if n == elements.len() => {
                        if n == 1 {
                            f.write_str(",")?;
                        }
                        f.write_str(")")?;
                    }
                    n => {
                        debug_assert!(n < elements.len());
                        f.write_str(", ")?
                    }
                },
                Pattern::Array(elements) => match data.n_children_yielded {
                    0 => {
                        f.write_str("[")?;
                        if 0 == elements.len() {
                            f.write_str("]")?;
                        }
                    }
                    n if n == elements.len() => {
                        f.write_str("]")?;
                    }
                    n => {
                        debug_assert!(n < elements.len());
                        f.write_str(", ")?;
                    }
                },
            }
        }

        Ok(())
    }
}

/// Identifier of a variable.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Identifier(Arc<str>);

impl Identifier {
    pub fn from_str_unchecked(str: &str) -> Self {
        Self(Arc::from(str))
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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
    UnwrapLeft,
    /// Right unwrap function.
    UnwrapRight,
    /// Some unwrap function.
    Unwrap,
}

/// String that is a jet name.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct JetName(Arc<str>);

impl JetName {
    /// Access the inner jet name.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for JetName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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
    /// A block expression executes a series of statements
    /// and returns the value of the final expression.
    Block(Vec<Statement>, Arc<Expression>),
    /// A single expression directly returns a value.
    Single(SingleExpression),
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
    /// Left wrapper expression
    Left(Arc<Expression>),
    /// Right wrapper expression
    Right(Arc<Expression>),
    /// None literal expression
    None,
    /// Some wrapper expression
    Some(Arc<Expression>),
    /// False literal expression
    False,
    /// True literal expression
    True,
    /// Unsigned integer literal expression
    UnsignedInteger(UnsignedDecimal),
    /// Bit string literal expression
    BitString(Bits),
    /// Byte string literal expression
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
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct UnsignedDecimal(Arc<str>);

impl UnsignedDecimal {
    /// Access the inner decimal string.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for UnsignedDecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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

    /// Convert the bit string into a Simplicity type.
    pub fn to_simplicity(&self) -> Arc<Value> {
        match &self.0 {
            BitsInner::U1(byte) => Value::u1(*byte),
            BitsInner::U2(byte) => Value::u2(*byte),
            BitsInner::U4(byte) => Value::u4(*byte),
            BitsInner::Long(bytes) => Value::power_of_two(bytes),
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

impl Bytes {
    /// Convert the byte string into a Simplicity value.
    pub fn to_simplicity(&self) -> Arc<Value> {
        Value::power_of_two(self.0.as_ref())
    }
}

/// String that is a witness name.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct WitnessName(Arc<str>);

impl WitnessName {
    /// Access the inner witness name.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for WitnessName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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
    Left(Identifier),
    /// Bind inner value of right value to variable name.
    Right(Identifier),
    /// Match none value (no binding).
    None,
    /// Bind inner value of some value to variable name.
    Some(Identifier),
    /// Match false value (no binding).
    False,
    /// Match true value (no binding).
    True,
}

impl MatchPattern {
    /// Get the variable identifier bound in the pattern.
    pub fn get_identifier(&self) -> Option<&Identifier> {
        match self {
            MatchPattern::Left(i) | MatchPattern::Right(i) | MatchPattern::Some(i) => Some(i),
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }
}

impl fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchPattern::Left(i) => write!(f, "Left({i}"),
            MatchPattern::Right(i) => write!(f, "Right({i}"),
            MatchPattern::None => write!(f, "None"),
            MatchPattern::Some(i) => write!(f, "Some({i}"),
            MatchPattern::False => write!(f, "false"),
            MatchPattern::True => write!(f, "true"),
        }
    }
}

impl UIntType {
    /// Parse a decimal string for the type.
    pub fn parse_decimal(&self, decimal: &UnsignedDecimal) -> Result<Arc<Value>, Error> {
        if let UIntType::U256 = self {
            let u256 = decimal.as_inner().parse::<U256>().map_err(Error::from)?;
            return Ok(Value::u256_from_slice(u256.as_ref()));
        }
        match self {
            UIntType::U1 => decimal.as_inner().parse::<u8>().map(Value::u1),
            UIntType::U2 => decimal.as_inner().parse::<u8>().map(Value::u2),
            UIntType::U4 => decimal.as_inner().parse::<u8>().map(Value::u4),
            UIntType::U8 => decimal.as_inner().parse::<u8>().map(Value::u8),
            UIntType::U16 => decimal.as_inner().parse::<u16>().map(Value::u16),
            UIntType::U32 => decimal.as_inner().parse::<u32>().map(Value::u32),
            UIntType::U64 => decimal.as_inner().parse::<u64>().map(Value::u64),
            UIntType::U128 => decimal.as_inner().parse::<u128>().map(Value::u128),
            UIntType::U256 => unreachable!("Covered by previous if-let"),
        }
        .map_err(Error::from)
    }
}

pub trait PestParse: Sized {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError>;
}

impl PestParse for Program {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::program));
        let mut stmts = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::statement => stmts.push(Statement::parse(inner_pair)?),
                Rule::EOI => (),
                _ => unreachable!(),
            };
        }
        Ok(Program { statements: stmts })
    }
}

impl PestParse for Statement {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::statement));
        let inner_pair = pair.into_inner().next().unwrap();
        match inner_pair.as_rule() {
            Rule::assignment => Assignment::parse(inner_pair).map(Statement::Assignment),
            Rule::expression => Expression::parse(inner_pair).map(Statement::Expression),
            Rule::type_alias => TypeAlias::parse(inner_pair).map(Statement::TypeAlias),
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

impl PestParse for Pattern {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::pattern));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::identifier));
        let identifier = Arc::from(pair.as_str());
        Ok(Identifier(identifier))
    }
}

impl PestParse for Assignment {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::assignment));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::call_expr));
        let span = Span::from(&pair);
        let mut it = pair.into_inner();
        let name = CallName::parse(it.next().unwrap())?;
        let args_pair = it.next().unwrap();
        assert!(matches!(args_pair.as_rule(), Rule::call_args));
        let args = args_pair
            .into_inner()
            .map(Expression::parse)
            .collect::<Result<Arc<[Expression]>, _>>()?;

        Ok(Call { name, args, span })
    }
}

impl PestParse for CallName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::call_name));
        match pair.as_str() {
            "unwrap_left" => Ok(CallName::UnwrapLeft),
            "unwrap_right" => Ok(CallName::UnwrapRight),
            "unwrap" => Ok(CallName::Unwrap),
            _ => {
                let inner = pair.into_inner().next().unwrap();
                match inner.as_rule() {
                    Rule::jet => JetName::parse(inner).map(CallName::Jet),
                    _ => panic!("Corrupt grammar"),
                }
            }
        }
    }
}

impl PestParse for JetName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::jet));
        let jet_name = pair.as_str().strip_prefix("jet_").unwrap();
        Ok(Self(Arc::from(jet_name)))
    }
}

impl PestParse for TypeAlias {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::type_alias));
        let span = Span::from(&pair);
        let mut it = pair.into_inner();
        let name = Identifier::parse(it.next().unwrap())?;
        let ty = AliasedType::parse(it.next().unwrap())?;
        Ok(Self { name, ty, span })
    }
}

impl PestParse for Expression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        let span = Span::from(&pair);
        let pair = match pair.as_rule() {
            Rule::expression => pair.into_inner().next().unwrap(),
            Rule::block_expression | Rule::single_expression => pair,
            _ => unreachable!("Corrupt grammar"),
        };

        let inner = match pair.as_rule() {
            Rule::block_expression => {
                let mut stmts = Vec::new();
                let mut inner_pair = pair.into_inner();
                while let Some(Rule::statement) = inner_pair.peek().map(|x| x.as_rule()) {
                    stmts.push(Statement::parse(inner_pair.next().unwrap())?);
                }
                let expr = Expression::parse(inner_pair.next().unwrap())?;
                ExpressionInner::Block(stmts, Arc::new(expr))
            }
            Rule::single_expression => ExpressionInner::Single(SingleExpression::parse(pair)?),
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(Expression { inner, span })
    }
}

impl PestParse for SingleExpression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::single_expression));

        let span = Span::from(&pair);
        let inner_pair = pair.into_inner().next().unwrap();

        let inner = match inner_pair.as_rule() {
            Rule::left_expr => {
                let l = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Left(Expression::parse(l).map(Arc::new)?)
            }
            Rule::right_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Right(Expression::parse(r).map(Arc::new)?)
            }
            Rule::none_expr => SingleExpressionInner::None,
            Rule::some_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Some(Expression::parse(r).map(Arc::new)?)
            }
            Rule::false_expr => SingleExpressionInner::False,
            Rule::true_expr => SingleExpressionInner::True,
            Rule::call_expr => SingleExpressionInner::Call(Call::parse(inner_pair)?),
            Rule::bit_string => SingleExpressionInner::BitString(Bits::parse(inner_pair)?),
            Rule::byte_string => SingleExpressionInner::ByteString(Bytes::parse(inner_pair)?),
            Rule::unsigned_integer => {
                SingleExpressionInner::UnsignedInteger(UnsignedDecimal::parse(inner_pair)?)
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::unsigned_integer));
        let decimal = Arc::from(pair.as_str().replace('_', ""));
        Ok(Self(decimal))
    }
}

impl PestParse for Bits {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::bit_string));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::byte_string));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::witness_name));
        let name = Arc::from(pair.as_str());
        Ok(Self(name))
    }
}

impl PestParse for Match {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::match_expr));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::match_arm));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::match_pattern));
        let inner_pair = pair.into_inner().next().unwrap();
        let rule = inner_pair.as_rule();
        let ret = match rule {
            Rule::left_pattern | Rule::right_pattern | Rule::some_pattern => {
                let identifier_pair = inner_pair.into_inner().next().unwrap();
                let identifier = Identifier::parse(identifier_pair)?;

                match rule {
                    Rule::left_pattern => MatchPattern::Left(identifier),
                    Rule::right_pattern => MatchPattern::Right(identifier),
                    Rule::some_pattern => MatchPattern::Some(identifier),
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

        assert!(matches!(pair.as_rule(), Rule::ty));
        let pair = TyPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::identifier => {
                    let identifier = Identifier::parse(data.node.0)?;
                    output.push(Item::Type(AliasedType::alias(identifier)));
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
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::unsigned_type));
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
            | Rule::identifier => Tree::Nullary,
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
