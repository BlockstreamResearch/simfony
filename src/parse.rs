//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::elements::hex::FromHex;
use simplicity::Value;

use crate::error::{Error, RichError, WithSpan};
use crate::num::NonZeroPow2Usize;
use crate::types::{ResolvedType, TypeConstructible, UIntType};
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
#[derive(Clone, Debug, Hash)]
pub struct Program {
    /// The statements in the program.
    pub statements: Vec<Statement>,
}

/// A statement in a simplicity program.
#[derive(Clone, Debug, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// A function call.
    FuncCall(FuncCall),
}

/// Pattern for binding values to variables.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Pattern {
    /// Bind value to variable name.
    Identifier(Identifier),
    /// Do not bind.
    Ignore,
    /// Split product value. Bind components to first and second pattern, respectively.
    Product(Arc<Self>, Arc<Self>),
    /// Split array value. Bind components to balanced binary tree of patterns.
    Array(Arc<[Self]>),
}

impl Pattern {
    /// Construct a product pattern.
    pub fn product(l: Self, r: Self) -> Self {
        Self::Product(Arc::new(l), Arc::new(r))
    }

    /// Construct an array pattern.
    ///
    /// ## Error
    ///
    /// The array is empty.
    pub fn array<I: IntoIterator<Item = Self>>(array: I) -> Result<Self, Error> {
        let inner: Arc<_> = array.into_iter().collect();
        if inner.is_empty() {
            Err(Error::ArraySizeZero)
        } else {
            Ok(Self::Array(inner))
        }
    }
}

impl<'a> TreeLike for &'a Pattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Pattern::Identifier(_) | Pattern::Ignore => Tree::Nullary,
            Pattern::Product(l, r) => Tree::Binary(l, r),
            Pattern::Array(children) => Tree::Nary(children.iter().collect()),
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Pattern::Identifier(i) => write!(f, "{i}")?,
                Pattern::Ignore => write!(f, "_")?,
                Pattern::Product(..) => match data.n_children_yielded {
                    0 => write!(f, "(")?,
                    1 => write!(f, ",")?,
                    n => {
                        debug_assert!(n == 2);
                        write!(f, ")")?;
                    }
                },
                Pattern::Array(children) => match data.n_children_yielded {
                    0 => write!(f, "[")?,
                    n if n == children.len() => write!(f, "]")?,
                    _ => write!(f, ",")?,
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
#[derive(Clone, Debug, Hash)]
pub struct Assignment {
    /// The pattern.
    pub pattern: Pattern,
    /// The return type of the expression.
    pub ty: ResolvedType,
    /// The expression.
    pub expression: Expression,
    /// The source text associated with this assignment.
    pub source_text: Arc<str>,
    /// Area that this assignment spans in the source file.
    pub span: Span,
}

/// A function(jet) call.
///
/// The function name is the name of the jet.
/// The arguments are the arguments to the jet.
/// Since jets in simplicity operate on a single paired type,
/// the arguments are paired together.
/// jet(a, b, c, d) = jet(pair(pair(pair(a, b), c), d))
#[derive(Clone, Debug, Hash)]
pub struct FuncCall {
    /// The type of the function.
    pub func_type: FuncType,
    /// The arguments to the function.
    pub args: Arc<[Expression]>,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// Area that this call spans in the source file.
    pub span: Span,
}

/// A function(jet) name.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum FuncType {
    /// A jet name.
    Jet(JetName),
    /// Left unwrap function
    UnwrapLeft,
    /// Right unwrap function
    UnwrapRight,
    /// Some unwrap function
    Unwrap,
    /// A builtin function name.
    BuiltIn(Arc<str>),
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

/// An expression is something that returns a value.
#[derive(Clone, Debug, Hash)]
pub struct Expression {
    /// The kind of expression
    pub inner: ExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// Area that this expression spans in the source file.
    pub span: Span,
}

/// The kind of expression.
#[derive(Clone, Debug, Hash)]
pub enum ExpressionInner {
    /// A block expression executes a series of statements
    /// and returns the value of the final expression.
    BlockExpression(Vec<Statement>, Arc<Expression>),
    /// A single expression directly returns a value.
    SingleExpression(SingleExpression),
}

/// A single expression directly returns a value.
#[derive(Clone, Debug, Hash)]
pub struct SingleExpression {
    /// The kind of single expression
    pub inner: SingleExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// Area that this expression spans in the source file.
    pub span: Span,
}

/// The kind of single expression.
#[derive(Clone, Debug, Hash)]
pub enum SingleExpressionInner {
    /// Unit literal expression
    Unit,
    /// Left wrapper expression
    Left(Arc<Expression>),
    /// Right wrapper expression
    Right(Arc<Expression>),
    /// Product wrapper expression
    Product(Arc<Expression>, Arc<Expression>),
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
    FuncCall(FuncCall),
    /// Expression in parentheses
    Expression(Arc<Expression>),
    /// Match expression over a sum type
    Match {
        /// Expression whose output is matched
        scrutinee: Arc<Expression>,
        /// Arm for left sum values
        left: MatchArm,
        /// Arm for right sum values
        right: MatchArm,
    },
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
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Bits {
    /// Least significant bit of byte
    U1(u8),
    /// Two least significant bits of byte
    U2(u8),
    /// Four least significant bits of byte
    U4(u8),
    /// All bits from byte string
    Long(Arc<[u8]>),
}

impl Bits {
    /// Convert the bit string into a Simplicity type.
    pub fn to_simplicity(&self) -> Arc<Value> {
        match self {
            Bits::U1(byte) => Value::u1(*byte),
            Bits::U2(byte) => Value::u2(*byte),
            Bits::U4(byte) => Value::u4(*byte),
            Bits::Long(bytes) => Value::power_of_two(bytes),
        }
    }
}

/// Byte string whose length is a power of two.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Bytes(pub Arc<[u8]>);

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

/// Arm of a match expression.
#[derive(Clone, Debug, Hash)]
pub struct MatchArm {
    /// Matched pattern
    pub pattern: MatchPattern,
    /// Executed expression
    pub expression: Arc<Expression>,
}

/// Pattern of a match arm.
#[derive(Clone, Debug, Hash)]
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

impl UIntType {
    /// Parse a decimal string for the type.
    pub fn parse_decimal(&self, decimal: &UnsignedDecimal) -> Result<Arc<Value>, Error> {
        if let UIntType::U128 | UIntType::U256 = self {
            return Err(Error::InvalidDecimal(*self));
        }

        match self {
            UIntType::U1 => decimal.as_inner().parse::<u8>().map(Value::u1),
            UIntType::U2 => decimal.as_inner().parse::<u8>().map(Value::u2),
            UIntType::U4 => decimal.as_inner().parse::<u8>().map(Value::u4),
            UIntType::U8 => decimal.as_inner().parse::<u8>().map(Value::u8),
            UIntType::U16 => decimal.as_inner().parse::<u16>().map(Value::u16),
            UIntType::U32 => decimal.as_inner().parse::<u32>().map(Value::u32),
            UIntType::U64 => decimal.as_inner().parse::<u64>().map(Value::u64),
            _ => unreachable!("Covered by outer match"),
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
            Rule::func_call => FuncCall::parse(inner_pair).map(Statement::FuncCall),
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
                Rule::product_pattern => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(Pattern::Product(Arc::new(l), Arc::new(r)));
                }
                Rule::array_pattern => {
                    assert!(0 < data.node.n_children(), "Array must be nonempty");
                    let children = output.split_off(output.len() - data.node.n_children());
                    let array = Pattern::array(children).with_span(&data.node.0)?;
                    output.push(array);
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
        let source_text = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let mut inner_pair = pair.into_inner();
        let pattern = Pattern::parse(inner_pair.next().unwrap())?;
        let ty = ResolvedType::parse(inner_pair.next().unwrap())?;
        let expression = Expression::parse(inner_pair.next().unwrap())?;
        Ok(Assignment {
            pattern,
            ty,
            expression,
            source_text,
            span,
        })
    }
}

impl PestParse for FuncCall {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::func_call));
        let source_text = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let inner_pair = pair.into_inner().next().unwrap();

        let func_type = FuncType::parse(inner_pair.clone())?;
        let inner_inner = inner_pair.into_inner();
        let mut args = Vec::new();
        for inner_inner_pair in inner_inner {
            match inner_inner_pair.as_rule() {
                Rule::expression => args.push(Expression::parse(inner_inner_pair)?),
                Rule::jet => {}
                _ => unreachable!("Corrupt grammar"),
            }
        }

        Ok(FuncCall {
            func_type,
            args: args.into_iter().collect(),
            source_text,
            span,
        })
    }
}

impl PestParse for FuncType {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        match pair.as_rule() {
            Rule::jet_expr => {
                let jet_pair = pair.into_inner().next().unwrap();
                JetName::parse(jet_pair).map(FuncType::Jet)
            }
            Rule::unwrap_left_expr => Ok(FuncType::UnwrapLeft),
            Rule::unwrap_right_expr => Ok(FuncType::UnwrapRight),
            Rule::unwrap_expr => Ok(FuncType::Unwrap),
            _ => unreachable!("Corrupt grammar"),
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

impl PestParse for Expression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        let source_text = Arc::from(pair.as_str());
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
                ExpressionInner::BlockExpression(stmts, Arc::new(expr))
            }
            Rule::single_expression => {
                ExpressionInner::SingleExpression(SingleExpression::parse(pair)?)
            }
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(Expression {
            inner,
            source_text,
            span,
        })
    }
}

impl PestParse for SingleExpression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::single_expression));

        let source_text: Arc<str> = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let inner_pair = pair.into_inner().next().unwrap();

        let inner = match inner_pair.as_rule() {
            Rule::unit_expr => SingleExpressionInner::Unit,
            Rule::left_expr => {
                let l = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Left(Expression::parse(l).map(Arc::new)?)
            }
            Rule::right_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Right(Expression::parse(r).map(Arc::new)?)
            }
            Rule::product_expr => {
                let mut product_pair = inner_pair.into_inner();
                let l = product_pair.next().unwrap();
                let r = product_pair.next().unwrap();
                SingleExpressionInner::Product(
                    Expression::parse(l).map(Arc::new)?,
                    Expression::parse(r).map(Arc::new)?,
                )
            }
            Rule::none_expr => SingleExpressionInner::None,
            Rule::some_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Some(Expression::parse(r).map(Arc::new)?)
            }
            Rule::false_expr => SingleExpressionInner::False,
            Rule::true_expr => SingleExpressionInner::True,
            Rule::func_call => SingleExpressionInner::FuncCall(FuncCall::parse(inner_pair)?),
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
            Rule::match_expr => {
                let mut it = inner_pair.into_inner();
                let scrutinee_pair = it.next().unwrap();
                let scrutinee = Expression::parse(scrutinee_pair.clone()).map(Arc::new)?;
                let first_arm = MatchArm::parse(it.next().unwrap())?;
                let second_arm = MatchArm::parse(it.next().unwrap())?;

                let (left, right) = match (&first_arm.pattern, &second_arm.pattern) {
                    (MatchPattern::Left(..), MatchPattern::Right(..)) => (first_arm, second_arm),
                    (MatchPattern::Left(..), _) => {
                        return Err(Error::UnmatchedPattern("Right".to_string()))
                            .with_span(&scrutinee_pair)
                    }
                    (MatchPattern::Right(..), MatchPattern::Left(..)) => (second_arm, first_arm),
                    (MatchPattern::Right(..), _) => {
                        return Err(Error::UnmatchedPattern("Left".to_string()))
                            .with_span(&scrutinee_pair)
                    }
                    (MatchPattern::None, MatchPattern::Some(..)) => (first_arm, second_arm),
                    (MatchPattern::None, _) => {
                        return Err(Error::UnmatchedPattern("Some".to_string()))
                            .with_span(&scrutinee_pair)
                    }
                    (MatchPattern::Some(..), MatchPattern::None) => (second_arm, first_arm),
                    (MatchPattern::Some(..), _) => {
                        return Err(Error::UnmatchedPattern("None".to_string()))
                            .with_span(&scrutinee_pair)
                    }
                    (MatchPattern::False, MatchPattern::True) => (first_arm, second_arm),
                    (MatchPattern::False, _) => {
                        return Err(Error::UnmatchedPattern("true".to_string()))
                            .with_span(&scrutinee_pair)
                    }
                    (MatchPattern::True, MatchPattern::False) => (second_arm, first_arm),
                    (MatchPattern::True, _) => {
                        return Err(Error::UnmatchedPattern("false".to_string()))
                            .with_span(&scrutinee_pair)
                    }
                };

                SingleExpressionInner::Match {
                    scrutinee,
                    left,
                    right,
                }
            }
            Rule::array_expr => {
                let elements: Arc<_> = inner_pair
                    .clone()
                    .into_inner()
                    .map(|inner| Expression::parse(inner))
                    .collect::<Result<Arc<_>, _>>()?;
                if elements.is_empty() {
                    return Err(Error::ArraySizeZero).with_span(&inner_pair);
                }
                SingleExpressionInner::Array(elements)
            }
            Rule::list_expr => {
                let elements = inner_pair
                    .into_inner()
                    .map(|inner| Expression::parse(inner))
                    .collect::<Result<Arc<_>, _>>()?;
                SingleExpressionInner::List(elements)
            }
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(SingleExpression {
            inner,
            source_text,
            span,
        })
    }
}

impl PestParse for UnsignedDecimal {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::unsigned_integer));
        let decimal = Arc::from(pair.as_str());
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
            return Err(Error::BitStringPow2).with_span(&pair);
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

        let ret = match bits.len() {
            1 => {
                debug_assert!(bytes[0] < 2);
                Bits::U1(bytes[0])
            }
            2 => {
                debug_assert!(bytes[0] < 4);
                Bits::U2(bytes[0])
            }
            4 => {
                debug_assert!(bytes[0] < 16);
                Bits::U4(bytes[0])
            }
            _ => Bits::Long(bytes.into_iter().collect()),
        };
        Ok(ret)
    }
}

impl PestParse for Bytes {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::byte_string));
        let hex_string = pair.as_str();
        debug_assert!(&hex_string[0..2] == "0x");

        let hex_digits = &hex_string[2..];
        if !hex_digits.len().is_power_of_two() {
            return Err(Error::HexStringPow2).with_span(&pair);
        }

        Vec::<u8>::from_hex(hex_digits)
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

impl PestParse for ResolvedType {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        enum Item {
            Type(ResolvedType),
            Size(NonZeroUsize),
            Bound(NonZeroPow2Usize),
        }

        impl Item {
            fn unwrap_type(self) -> ResolvedType {
                match self {
                    Item::Type(ty) => ty,
                    _ => panic!("Not a type"),
                }
            }

            fn unwrap_size(self) -> NonZeroUsize {
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
                Rule::unit_type => output.push(Item::Type(ResolvedType::unit())),
                Rule::unsigned_type => {
                    let uint_ty = UIntType::parse(data.node.0)?;
                    output.push(Item::Type(ResolvedType::uint(uint_ty)));
                }
                Rule::sum_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    let l = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(ResolvedType::either(l, r)));
                }
                Rule::product_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    let l = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(ResolvedType::product(l, r)));
                }
                Rule::option_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(ResolvedType::option(r)));
                }
                Rule::boolean_type => {
                    output.push(Item::Type(ResolvedType::boolean()));
                }
                Rule::array_type => {
                    let size = output.pop().unwrap().unwrap_size();
                    let el = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(ResolvedType::array(el, size)));
                }
                Rule::array_size => {
                    let size_str = data.node.0.as_str();
                    let size = size_str
                        .parse::<NonZeroUsize>()
                        .map_err(|_| Error::ArraySizeZero)
                        .with_span(&data.node.0)?;
                    output.push(Item::Size(size));
                }
                Rule::list_type => {
                    let bound = output.pop().unwrap().unwrap_bound();
                    let el = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(ResolvedType::list(el, bound)));
                }
                Rule::list_bound => {
                    let bound_str = data.node.0.as_str();
                    let bound = bound_str
                        .parse::<NonZeroPow2Usize>()
                        .map_err(|_| Error::ListBoundPow2)
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
            Rule::product_pattern => {
                let l = it.next().unwrap();
                let r = it.next().unwrap();
                Tree::Binary(PatternPair(l), PatternPair(r))
            }
            Rule::array_pattern => {
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
            Rule::unit_type
            | Rule::boolean_type
            | Rule::unsigned_type
            | Rule::array_size
            | Rule::list_bound => Tree::Nullary,
            Rule::ty | Rule::option_type => {
                let l = it.next().unwrap();
                Tree::Unary(TyPair(l))
            }
            Rule::sum_type | Rule::product_type | Rule::array_type | Rule::list_type => {
                let l = it.next().unwrap();
                let r = it.next().unwrap();
                Tree::Binary(TyPair(l), TyPair(r))
            }
            _ => unreachable!("Corrupt grammar"),
        }
    }
}
