//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::elements::hex::FromHex;
use simplicity::types::Type as SimType;
use simplicity::Value;

use crate::Rule;

/// A complete simplicity program.
#[derive(Debug)]
pub struct Program {
    /// The statements in the program.
    pub statements: Vec<Statement>,
}

/// A statement in a simplicity program.
#[derive(Debug)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// A declaration of a witness.
    WitnessDecl(WitnessName),
    /// A function call.
    FuncCall(FuncCall),
}

/// Pattern for binding values to variables.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Bind value to variable name.
    Identifier(Identifier),
    /// Do not bind.
    Ignore,
    /// Split product value. Bind components to first and second pattern, respectively.
    Product(Arc<Self>, Arc<Self>),
}

impl<'a> TreeLike for &'a Pattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Pattern::Identifier(_) | Pattern::Ignore => Tree::Nullary,
            Pattern::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

/// Identifier of a variable.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Identifier(Arc<str>);

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The output of an expression is assigned to a pattern.
#[derive(Debug)]
pub struct Assignment {
    /// The pattern.
    pub pattern: Pattern,
    /// The return type of the expression.
    pub ty: Option<Type>,
    /// The expression.
    pub expression: Expression,
    /// The source text associated with this assignment.
    pub source_text: Arc<str>,
    /// The position of this assignment in the source file. (row, col)
    pub position: (usize, usize),
}

/// A function(jet) call.
///
/// The function name is the name of the jet.
/// The arguments are the arguments to the jet.
/// Since jets in simplicity operate on a single paired type,
/// the arguments are paired together.
/// jet(a, b, c, d) = jet(pair(pair(pair(a, b), c), d))
#[derive(Debug)]
pub struct FuncCall {
    /// The type of the function.
    pub func_type: FuncType,
    /// The arguments to the function.
    pub args: Vec<Expression>,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// A function(jet) name.
#[derive(Debug)]
pub enum FuncType {
    /// A jet name.
    Jet(Arc<str>),
    /// Left unwrap function
    UnwrapLeft,
    /// Right unwrap function
    UnwrapRight,
    /// Some unwrap function
    Unwrap,
    /// A builtin function name.
    BuiltIn(Arc<str>),
}

/// An expression is something that returns a value.
#[derive(Debug)]
pub struct Expression {
    /// The kind of expression
    pub inner: ExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// The kind of expression.
#[derive(Debug)]
pub enum ExpressionInner {
    /// A block expression executes a series of statements
    /// and returns the value of the final expression.
    BlockExpression(Vec<Statement>, Arc<Expression>),
    /// A single expression directly returns a value.
    SingleExpression(SingleExpression),
}

/// A single expression directly returns a value.
#[derive(Debug)]
pub struct SingleExpression {
    /// The kind of single expression
    pub inner: SingleExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// The kind of single expression.
#[derive(Debug)]
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
    /// Unsigned integer literal expression
    UnsignedInteger(Arc<str>),
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
}

/// Bit string whose length is a power of two.
#[derive(Clone, Debug)]
pub enum Bits {
    /// Least significant bit of byte
    U1(u8),
    /// Two least significant bits of byte
    U2(u8),
    /// Four least significant bits of byte
    U4(u8),
    /// All bits from byte string
    Long(Vec<u8>),
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
#[derive(Clone, Debug)]
pub struct Bytes(pub Vec<u8>);

impl Bytes {
    /// Convert the byte string into a Simplicity value.
    pub fn to_simplicity(&self) -> Arc<Value> {
        Value::power_of_two(self.0.as_ref())
    }
}

/// String that is a witness name.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
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

/// A Simphony type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[non_exhaustive]
pub enum Type {
    Unit,
    Either(Arc<Self>, Arc<Self>),
    Product(Arc<Self>, Arc<Self>),
    Option(Arc<Self>),
    UInt(UIntType),
}

/// Normalized unsigned integer type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum UIntType {
    U1,
    U2,
    U4,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256,
}

impl<'a> TreeLike for &'a Type {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Type::Unit | Type::UInt(..) => Tree::Nullary,
            Type::Option(r) => Tree::Unary(r),
            Type::Either(l, r) | Type::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

impl Type {
    /// Convert the type into a normalized unsigned integer type.
    /// Return the empty value if the conversion failed.
    pub fn to_uint(&self) -> Option<UIntType> {
        let mut integer_type = HashMap::<&Type, UIntType>::new();
        for data in self.post_order_iter() {
            match data.node {
                Type::Unit => {}
                Type::Either(l, r) => match (l.as_ref(), r.as_ref()) {
                    (Type::Unit, Type::Unit) => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                Type::Product(l, r) => {
                    let uint_l = integer_type.get(l.as_ref())?;
                    let uint_r = integer_type.get(r.as_ref())?;
                    if uint_l != uint_r {
                        return None;
                    }
                    let uint_ty = uint_l.double()?;
                    integer_type.insert(data.node, uint_ty);
                }
                Type::Option(r) => match r.as_ref() {
                    Type::Unit => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                Type::UInt(ty) => {
                    integer_type.insert(data.node, *ty);
                }
            }
        }

        integer_type.remove(self)
    }

    /// Convert the type into a Simplicity type.
    pub fn to_simplicity(&self) -> SimType {
        let mut output = vec![];

        for data in self.post_order_iter() {
            match data.node {
                Type::Unit => output.push(SimType::unit()),
                Type::Either(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::sum(l, r));
                }
                Type::Product(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::product(l, r));
                }
                Type::Option(_) => {
                    let r = output.pop().unwrap();
                    output.push(SimType::sum(SimType::unit(), r));
                }
                Type::UInt(ty) => output.push(ty.to_simplicity()),
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Type::Unit => f.write_str("1")?,
                Type::Either(_, _) => match data.n_children_yielded {
                    0 => f.write_str("Either<")?,
                    1 => f.write_str(",")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(">")?;
                    }
                },
                Type::Product(_, _) => match data.n_children_yielded {
                    0 => f.write_str("(")?,
                    1 => f.write_str(",")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(")")?;
                    }
                },
                Type::Option(_) => match data.n_children_yielded {
                    0 => f.write_str("Option<")?,
                    n => {
                        debug_assert!(n == 1);
                        f.write_str(">")?;
                    }
                },
                Type::UInt(ty) => write!(f, "{ty}")?,
            }
        }

        Ok(())
    }
}

impl UIntType {
    /// Double the bit width of the type.
    /// Return the empty value upon overflow.
    pub fn double(&self) -> Option<Self> {
        match self {
            UIntType::U1 => Some(UIntType::U2),
            UIntType::U2 => Some(UIntType::U4),
            UIntType::U4 => Some(UIntType::U8),
            UIntType::U8 => Some(UIntType::U16),
            UIntType::U16 => Some(UIntType::U32),
            UIntType::U32 => Some(UIntType::U64),
            UIntType::U64 => Some(UIntType::U128),
            UIntType::U128 => Some(UIntType::U256),
            UIntType::U256 => None,
        }
    }

    /// Parse a decimal string for the type.
    pub fn parse_decimal(&self, literal: &str) -> Arc<Value> {
        match self {
            UIntType::U1 => Value::u1(literal.parse::<u8>().unwrap()),
            UIntType::U2 => Value::u2(literal.parse::<u8>().unwrap()),
            UIntType::U4 => Value::u4(literal.parse::<u8>().unwrap()),
            UIntType::U8 => Value::u8(literal.parse::<u8>().unwrap()),
            UIntType::U16 => Value::u16(literal.parse::<u16>().unwrap()),
            UIntType::U32 => Value::u32(literal.parse::<u32>().unwrap()),
            UIntType::U64 => Value::u64(literal.parse::<u64>().unwrap()),
            UIntType::U128 => panic!("Use bit or hex strings for u128"),
            UIntType::U256 => panic!("Use bit or hex strings for u256"),
        }
    }

    /// Convert the type into a Simplicity type.
    pub fn to_simplicity(&self) -> SimType {
        match self {
            UIntType::U1 => SimType::two_two_n(0),
            UIntType::U2 => SimType::two_two_n(1),
            UIntType::U4 => SimType::two_two_n(2),
            UIntType::U8 => SimType::two_two_n(3),
            UIntType::U16 => SimType::two_two_n(4),
            UIntType::U32 => SimType::two_two_n(5),
            UIntType::U64 => SimType::two_two_n(6),
            UIntType::U128 => SimType::two_two_n(7),
            UIntType::U256 => SimType::two_two_n(8),
        }
    }
}

impl fmt::Display for UIntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UIntType::U1 => f.write_str("u1"),
            UIntType::U2 => f.write_str("u2"),
            UIntType::U4 => f.write_str("u4"),
            UIntType::U8 => f.write_str("u8"),
            UIntType::U16 => f.write_str("u16"),
            UIntType::U32 => f.write_str("u32"),
            UIntType::U64 => f.write_str("u64"),
            UIntType::U128 => f.write_str("u128"),
            UIntType::U256 => f.write_str("u256"),
        }
    }
}

pub trait PestParse {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self;
}

impl PestParse for Program {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::program));
        let mut stmts = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::statement => stmts.push(Statement::parse(inner_pair)),
                Rule::EOI => (),
                _ => unreachable!(),
            };
        }
        Program { statements: stmts }
    }
}

impl PestParse for Statement {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::statement));
        let inner_pair = pair.into_inner().next().unwrap();
        match inner_pair.as_rule() {
            Rule::assignment => Statement::Assignment(Assignment::parse(inner_pair)),
            Rule::witness => Statement::WitnessDecl(WitnessName::parse(inner_pair)),
            Rule::func_call => Statement::FuncCall(FuncCall::parse(inner_pair)),
            x => panic!("{:?}", x),
        }
    }
}

impl PestParse for Pattern {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::pattern));
        let pair = PatternPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::pattern => {}
                Rule::variable_pattern => {
                    let identifier = Identifier::parse(data.node.0.into_inner().next().unwrap());
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
                _ => unreachable!("Corrupt grammar"),
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

impl PestParse for Identifier {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::identifier));
        let identifier = Arc::from(pair.as_str());
        Identifier(identifier)
    }
}

impl PestParse for Assignment {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::assignment));
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
        let mut inner_pair = pair.into_inner();
        let pattern = Pattern::parse(inner_pair.next().unwrap());
        let reqd_ty = if let Rule::ty = inner_pair.peek().unwrap().as_rule() {
            Some(Type::parse(inner_pair.next().unwrap()))
        } else {
            None
        };
        let expression = Expression::parse(inner_pair.next().unwrap());
        Assignment {
            pattern,
            ty: reqd_ty,
            expression,
            source_text,
            position,
        }
    }
}

impl PestParse for FuncCall {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::func_call));
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
        let inner_pair = pair.into_inner().next().unwrap();

        let func_type = FuncType::parse(inner_pair.clone());
        let inner_inner = inner_pair.into_inner();
        let mut args = Vec::new();
        for inner_inner_pair in inner_inner {
            match inner_inner_pair.as_rule() {
                Rule::expression => args.push(Expression::parse(inner_inner_pair)),
                Rule::jet => {}
                _ => unreachable!("Corrupt grammar"),
            }
        }

        FuncCall {
            func_type,
            args,
            source_text,
            position,
        }
    }
}

impl PestParse for FuncType {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        match pair.as_rule() {
            Rule::jet_expr => {
                let jet_pair = pair.into_inner().next().unwrap();
                let jet_name = jet_pair.as_str().strip_prefix("jet_").unwrap();
                FuncType::Jet(Arc::from(jet_name))
            }
            Rule::unwrap_left_expr => FuncType::UnwrapLeft,
            Rule::unwrap_right_expr => FuncType::UnwrapRight,
            Rule::unwrap_expr => FuncType::Unwrap,
            rule => panic!("Cannot parse rule: {:?}", rule),
        }
    }
}

impl PestParse for Expression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::expression));

        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
        let pair = pair.into_inner().next().unwrap();

        let inner = match pair.as_rule() {
            Rule::block_expression => {
                let mut stmts = Vec::new();
                let mut inner_pair = pair.into_inner();
                while let Some(Rule::statement) = inner_pair.peek().map(|x| x.as_rule()) {
                    stmts.push(Statement::parse(inner_pair.next().unwrap()));
                }
                let expr = Expression::parse(inner_pair.next().unwrap());
                ExpressionInner::BlockExpression(stmts, Arc::new(expr))
            }
            Rule::single_expression => {
                ExpressionInner::SingleExpression(SingleExpression::parse(pair))
            }
            _ => unreachable!("Corrupt grammar"),
        };

        Expression {
            inner,
            source_text,
            position,
        }
    }
}

impl PestParse for SingleExpression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::single_expression));

        let source_text: Arc<str> = Arc::from(pair.as_str());
        let position = pair.line_col();
        let inner_pair = pair.into_inner().next().unwrap();

        let inner = match inner_pair.as_rule() {
            Rule::unit_expr => SingleExpressionInner::Unit,
            Rule::left_expr => {
                let l = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Left(Arc::new(Expression::parse(l)))
            }
            Rule::right_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Right(Arc::new(Expression::parse(r)))
            }
            Rule::product_expr => {
                let mut product_pair = inner_pair.into_inner();
                let l = product_pair.next().unwrap();
                let r = product_pair.next().unwrap();
                SingleExpressionInner::Product(
                    Arc::new(Expression::parse(l)),
                    Arc::new(Expression::parse(r)),
                )
            }
            Rule::none_expr => SingleExpressionInner::None,
            Rule::some_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Some(Arc::new(Expression::parse(r)))
            }
            Rule::func_call => SingleExpressionInner::FuncCall(FuncCall::parse(inner_pair)),
            Rule::bit_string => SingleExpressionInner::BitString(Bits::parse(inner_pair)),
            Rule::byte_string => SingleExpressionInner::ByteString(Bytes::parse(inner_pair)),
            Rule::unsigned_integer => SingleExpressionInner::UnsignedInteger(source_text.clone()),
            Rule::witness_expr => {
                let witness_pair = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Witness(WitnessName::parse(witness_pair))
            }
            Rule::variable_expr => {
                let identifier_pair = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Variable(Identifier::parse(identifier_pair))
            }
            Rule::expression => {
                SingleExpressionInner::Expression(Arc::new(Expression::parse(inner_pair)))
            }
            _ => unreachable!("Corrupt grammar"),
        };

        SingleExpression {
            inner,
            source_text,
            position,
        }
    }
}

impl PestParse for Bits {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::bit_string));
        let bit_string = pair.as_str();
        assert_eq!(&bit_string[0..2], "0b");

        let bits = &bit_string[2..];
        if !bits.len().is_power_of_two() {
            panic!("Length of bit strings must be a power of two");
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
            _ => Bits::Long(bytes),
        }
    }
}

impl PestParse for Bytes {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::byte_string));
        let hex_string = pair.as_str();
        assert_eq!(&hex_string[0..2], "0x");

        let hex_digits = &hex_string[2..];
        if !hex_digits.len().is_power_of_two() {
            panic!("Length of hex strings must be a power of two");
        }

        let bytes = Vec::<u8>::from_hex(hex_digits).unwrap();
        Bytes(bytes)
    }
}

impl PestParse for WitnessName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::witness));
        let name = Arc::from(pair.as_str());
        WitnessName(name)
    }
}

impl PestParse for Type {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::ty));
        let pair = TyPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::unit_type => output.push(Type::Unit),
                Rule::unsigned_type => {
                    let uint_ty = UIntType::parse(data.node.0);
                    output.push(Type::UInt(uint_ty));
                }
                Rule::sum_type => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(Type::Either(Arc::new(l), Arc::new(r)));
                }
                Rule::product_type => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(Type::Product(Arc::new(l), Arc::new(r)));
                }
                Rule::option_type => {
                    let r = output.pop().unwrap();
                    output.push(Type::Option(Arc::new(r)));
                }
                Rule::ty => {}
                _ => unreachable!("Corrupt grammar"),
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

impl PestParse for UIntType {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::unsigned_type));
        match pair.as_str() {
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
        }
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
            Rule::unit_type | Rule::unsigned_type => Tree::Nullary,
            Rule::ty | Rule::option_type => {
                let l = it.next().unwrap();
                Tree::Unary(TyPair(l))
            }
            Rule::sum_type | Rule::product_type => {
                let l = it.next().unwrap();
                let r = it.next().unwrap();
                Tree::Binary(TyPair(l), TyPair(r))
            }
            _ => unreachable!("Corrupt grammar"),
        }
    }
}
