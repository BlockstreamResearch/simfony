//! This module contains the parsing code to convert the
//! tokens into an AST.

use core::fmt;
use std::str::FromStr;

use simplicity::{hex::FromHex, types, Value};

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
    /// Destruct an assignment
    DestructTuple(DestructPair),
    /// A declaration of a variable.
    Assignment(Assignment),
    /// A declaration of a witness.
    WitnessDecl(String),
    /// A function call.
    FuncCall(FuncCall),
}

#[derive(Debug)]
pub struct DestructPair {
    /// The name of the left variable.
    pub l_ident: String,
    /// The name of the right variable.
    pub r_ident: String,
    /// The type of the variable.
    pub ty: Option<Type>,
    /// The expression that the variable is assigned to.
    pub expression: Expression,
}

/// A variable declaration.
#[derive(Debug)]
pub struct Assignment {
    /// The name of the variable.
    pub identifier: String,
    /// The type of the variable.
    pub ty: Option<Type>,
    /// The expression that the variable is assigned to.
    pub expression: Expression,
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
    /// The name of the function.
    pub func_name: FuncType,
    /// The arguments to the function.
    pub args: Vec<Expression>,
}

/// A function(jet) name.
#[derive(Debug)]
pub enum FuncType {
    /// A jet name.
    Jet(String),
    /// A builtin function name.
    BuiltIn(String),
}

/// An expression.
#[derive(Debug)]
pub enum Expression {
    /// A block expression.
    BlockExpression(Vec<Statement>, Box<Expression>),
    /// A pair expression.
    Pair(Box<Expression>, Box<Expression>),
    /// A single expression.
    SingleExpression(Box<SingleExpression>),
}

/// A single without any blocks or pairs
#[derive(Debug)]
pub enum SingleExpression {
    /// A term.
    Term(Box<Term>),
}

/// A terminal.
#[derive(Debug)]
pub enum Term {
    /// Constant
    Constants(Constants),
    /// A witness identifier
    Witness(String),
    /// A (jet)function call
    FuncCall(FuncCall),
    /// A variable identifier
    Identifier(String),
    /// An expression in parentheses.
    Expression(Expression),
}

/// A constant.
#[derive(Debug)]
pub enum Constants {
    /// unit
    Unit,
    /// none
    None,
    /// false
    False,
    /// true
    True,
    /// A number
    Number(String),
}

/// The type of a value being parsed.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[non_exhaustive]
pub enum Type {
    U1,
    U2,
    U4,
    U8,
    U16,
    U32,
    U64,
    U256, // Same as pubkey for now. But we can add EC point checks on (Xonly)pubkey later
    Pubkey,
}

impl Type {
    /// Parse a number from a string for the given type
    /// and return the corresponding value.
    pub fn parse_num(&self, s: &str) -> Value {
        match self {
            Type::U1 => Value::u1(s.parse::<u8>().unwrap()),
            Type::U2 => Value::u2(s.parse::<u8>().unwrap()),
            Type::U4 => Value::u4(s.parse::<u8>().unwrap()),
            Type::U8 => Value::u8(s.parse::<u8>().unwrap()),
            Type::U16 => Value::u16(s.parse::<u16>().unwrap()),
            Type::U32 => Value::u32(s.parse::<u32>().unwrap()),
            Type::U64 => Value::u64(s.parse::<u64>().unwrap()),
            Type::Pubkey | Type::U256 => {
                let hex_decoded = Vec::<u8>::from_hex(&s[2..]).unwrap();
                Value::u256_from_slice(&hex_decoded)
            } // x => panic!("Unsupported type for number parsing {}", x),
        }
    }

    /// Convert to a Simplicity type
    pub fn to_simplicity_type(&self) -> types::Type {
        // TODO: Support specifying more types similar to andrew's code
        match self {
            Type::U1 => types::Type::two_two_n(0),
            Type::U2 => types::Type::two_two_n(1),
            Type::U4 => types::Type::two_two_n(2),
            Type::U8 => types::Type::two_two_n(3),
            Type::U16 => types::Type::two_two_n(4),
            Type::U32 => types::Type::two_two_n(5),
            Type::U64 => types::Type::two_two_n(6),
            Type::Pubkey | Type::U256 => types::Type::two_two_n(8), // cast OK as we are only using tiny numbers
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::U1 => write!(f, "u1"),
            Type::U2 => write!(f, "u2"),
            Type::U4 => write!(f, "u4"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::U256 => write!(f, "u256"),
            Type::Pubkey => write!(f, "pubkey"),
        }
    }
}

impl FromStr for Type {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "u1" => Ok(Type::U1),
            "u2" => Ok(Type::U2),
            "u4" => Ok(Type::U4),
            "u8" => Ok(Type::U8),
            "u16" => Ok(Type::U16),
            "u32" => Ok(Type::U32),
            "u64" => Ok(Type::U64),
            "u256" => Ok(Type::U256),
            "pubkey" => Ok(Type::Pubkey),
            _ => {
                panic!("Invalid type: {}", s);
            }
        }
    }
}

pub trait PestParse {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self;
}

impl PestParse for Statement {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let inner_pair = pair.into_inner().next().unwrap();
        match inner_pair.as_rule() {
            Rule::destruct_pair => Statement::DestructTuple(DestructPair::parse(inner_pair)),
            Rule::assignment => Statement::Assignment(Assignment::parse(inner_pair)),
            Rule::witness => Statement::WitnessDecl(parse_witness(inner_pair)),
            Rule::func_call => Statement::FuncCall(FuncCall::parse(inner_pair)),
            x => panic!("{:?}", x),
        }
    }
}

impl PestParse for DestructPair {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let mut inner_pair = pair.into_inner();
        let l_ident = inner_pair.next().unwrap().as_str();
        let r_ident = inner_pair.next().unwrap().as_str();

        let reqd_ty = if let Rule::ty = inner_pair.peek().unwrap().as_rule() {
            let ty = inner_pair.next().unwrap().as_str().parse::<Type>().unwrap();
            Some(ty)
        } else {
            None
        };
        let expression = Expression::parse(inner_pair.next().unwrap());
        DestructPair {
            l_ident: l_ident.to_string(),
            r_ident: r_ident.to_string(),
            ty: reqd_ty,
            expression,
        }
    }
}

impl PestParse for Assignment {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let mut inner_pair = pair.into_inner();
        let ident = inner_pair.next().unwrap().as_str();
        let reqd_ty = if let Rule::ty = inner_pair.peek().unwrap().as_rule() {
            let ty = inner_pair.next().unwrap().as_str().parse::<Type>().unwrap();
            Some(ty)
        } else {
            None
        };
        let expression = Expression::parse(inner_pair.next().unwrap());
        Assignment {
            identifier: ident.to_string(),
            ty: reqd_ty,
            expression,
        }
    }
}

impl PestParse for FuncCall {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let mut pair = pair.into_inner();
        let func_name_pair = pair.next().unwrap();
        let func_name = parse_func_name(func_name_pair);
        let mut args = Vec::new();
        for inner_pair in pair {
            match inner_pair.as_rule() {
                Rule::expression => args.push(Expression::parse(inner_pair)),
                x => panic!("{:?}", x),
            }
        }
        FuncCall { func_name, args }
    }
}

impl PestParse for Expression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::block_expression => {
                let mut stmts = Vec::new();
                let mut inner_pair = pair.into_inner();
                while let Some(Rule::statement) = inner_pair.peek().map(|x| x.as_rule()) {
                    stmts.push(Statement::parse(inner_pair.next().unwrap()));
                }
                let expr = Expression::parse(inner_pair.next().unwrap());
                Expression::BlockExpression(stmts, Box::new(expr))
            }
            Rule::pair => {
                let mut inner_pair = pair.into_inner();
                let lhs = Expression::parse(inner_pair.next().unwrap());
                let rhs = Expression::parse(inner_pair.next().unwrap());
                Expression::Pair(Box::new(lhs), Box::new(rhs))
            }
            Rule::single_expression => {
                Expression::SingleExpression(Box::new(SingleExpression::parse(pair)))
            }
            x => panic!("{:?}", x),
        }
    }
}

impl PestParse for SingleExpression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let mut pairs = pair.into_inner();
        let pair = pairs.next().unwrap();
        SingleExpression::Term(Box::new(Term::parse(pair)))
    }
}

impl PestParse for Term {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::constants => Term::Constants(Constants::parse(pair)),
            Rule::witness => Term::Witness(parse_witness(pair)),
            Rule::func_call => Term::FuncCall(FuncCall::parse(pair)),
            Rule::identifier => Term::Identifier(parse_identifier(pair)),
            Rule::expression => Term::Expression(Expression::parse(pair)),
            _x => panic!("{:?}", pair),
        }
    }
}

impl PestParse for Constants {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::unit => Constants::Unit,
            Rule::none => Constants::None,
            Rule::false_ => Constants::False,
            Rule::true_ => Constants::True,
            Rule::number => Constants::Number(pair.as_str().to_string()),
            x => unreachable!("expected constant {:?}, found", x),
        }
    }
}

// identifier = @{ !(reserved) ~ ASCII_ALPHA ~ (ASCII_ALPHANUMERIC)* }
pub fn parse_identifier(pair: pest::iterators::Pair<Rule>) -> String {
    match pair.as_rule() {
        Rule::identifier => pair.as_str().to_string(),
        x => {
            unreachable!("expected identifier found {:?}", x);
        }
    }
}

/// Parse a jet name
pub fn parse_func_name(pair: pest::iterators::Pair<Rule>) -> FuncType {
    match pair.as_rule() {
        Rule::jet => FuncType::Jet(pair.as_str().strip_prefix("jet_").unwrap().to_string()),
        Rule::builtin => {
            FuncType::BuiltIn(pair.as_str().strip_prefix("builtin_").unwrap().to_string())
        }
        x => {
            panic!("expected jet name found {:?}", x);
        }
    }
}

/// Parse a witness ident
pub fn parse_witness(pair: pest::iterators::Pair<Rule>) -> String {
    match pair.as_rule() {
        Rule::witness => pair.as_str().strip_prefix("wit_").unwrap().to_string(),
        x => {
            panic!("expected witness found: {:?}", x);
        }
    }
}
