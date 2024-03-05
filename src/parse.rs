//! This module contains the parsing code to convert the
//! tokens into an AST.

use core::fmt;
use std::{str::FromStr, sync::Arc};

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
    WitnessDecl(Arc<str>),
    /// A function call.
    FuncCall(FuncCall),
}

#[derive(Debug)]
pub struct DestructPair {
    /// The name of the left variable.
    pub l_ident: Arc<str>,
    /// The name of the right variable.
    pub r_ident: Arc<str>,
    /// The type of the variable.
    pub ty: Option<Type>,
    /// The expression that the variable is assigned to.
    pub expression: Expression,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// A variable declaration.
#[derive(Debug)]
pub struct Assignment {
    /// The name of the variable.
    pub identifier: Arc<str>,
    /// The type of the variable.
    pub ty: Option<Type>,
    /// The expression that the variable is assigned to.
    pub expression: Expression,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
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
    /// The name of the function.
    pub func_name: FuncType,
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
    /// AssertL function
    AssertL,
    /// AssertR function
    AssertR,
    /// A builtin function name.
    BuiltIn(Arc<str>),
}

/// An expression.
#[derive(Debug)]
pub struct Expression {
    /// The inner expression.
    pub inner: ExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// An expression inner.
#[derive(Debug)]
pub enum ExpressionInner {
    /// A block expression.
    BlockExpression(Vec<Statement>, Box<Expression>),
    /// A pair expression.
    Pair(Box<Expression>, Box<Expression>),
    /// A single expression.
    SingleExpression(Box<SingleExpression>),
}

/// A single without any blocks or pairs
#[derive(Debug)]
pub struct SingleExpression {
    /// A term.
    pub term: Box<Term>,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// A terminal.
#[derive(Debug)]
pub struct Term {
    /// The inner terminal.
    pub inner: TermInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// A terminal.
#[derive(Debug)]
pub enum TermInner {
    /// Constant
    Constants(Constants),
    /// A witness identifier
    Witness(Arc<str>),
    /// A (jet)function call
    FuncCall(FuncCall),
    /// A variable identifier
    Identifier(Arc<str>),
    /// An expression in parentheses.
    Expression(Expression),
}

/// A constant.
#[derive(Debug)]
pub struct Constants {
    /// The constant.
    pub inner: ConstantsInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// The position of this expression in the source file. (row, col)
    pub position: (usize, usize),
}

/// A constant inner.
#[derive(Debug)]
pub enum ConstantsInner {
    /// unit
    Unit,
    /// none
    None,
    /// false
    False,
    /// true
    True,
    /// A number
    Number(Arc<str>),
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
    pub fn parse_num(&self, s: &str) -> Arc<Value> {
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
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
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
            l_ident: Arc::from(l_ident),
            r_ident: Arc::from(r_ident),
            ty: reqd_ty,
            expression,
            source_text,
            position,
        }
    }
}

impl PestParse for Assignment {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::assignment));
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
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
            identifier: Arc::from(ident),
            ty: reqd_ty,
            expression,
            source_text,
            position,
        }
    }
}

impl PestParse for FuncCall {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
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
        FuncCall {
            func_name,
            args,
            source_text,
            position,
        }
    }
}

impl PestParse for Expression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
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
                ExpressionInner::BlockExpression(stmts, Box::new(expr))
            }
            Rule::pair => {
                let mut inner_pair = pair.into_inner();
                let lhs = Expression::parse(inner_pair.next().unwrap());
                let rhs = Expression::parse(inner_pair.next().unwrap());
                ExpressionInner::Pair(Box::new(lhs), Box::new(rhs))
            }
            Rule::single_expression => {
                ExpressionInner::SingleExpression(Box::new(SingleExpression::parse(pair)))
            }
            x => panic!("{:?}", x),
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
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
        let mut pairs = pair.into_inner();
        let pair = pairs.next().unwrap();
        SingleExpression {
            term: Box::new(Term::parse(pair)),
            source_text,
            position,
        }
    }
}

impl PestParse for Term {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
        let pair = pair.into_inner().next().unwrap();
        let inner = match pair.as_rule() {
            Rule::constants => TermInner::Constants(Constants::parse(pair)),
            Rule::witness => TermInner::Witness(parse_witness(pair)),
            Rule::func_call => TermInner::FuncCall(FuncCall::parse(pair)),
            Rule::identifier => TermInner::Identifier(parse_identifier(pair)),
            Rule::expression => TermInner::Expression(Expression::parse(pair)),
            _x => panic!("{:?}", pair),
        };
        Term {
            inner,
            source_text,
            position,
        }
    }
}

impl PestParse for Constants {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        let source_text = Arc::from(pair.as_str());
        let position = pair.line_col();
        let pair = pair.into_inner().next().unwrap();
        let inner = match pair.as_rule() {
            Rule::unit => ConstantsInner::Unit,
            Rule::none => ConstantsInner::None,
            Rule::false_ => ConstantsInner::False,
            Rule::true_ => ConstantsInner::True,
            Rule::number => ConstantsInner::Number(Arc::from(pair.as_str())),
            x => unreachable!("expected constant {:?}, found", x),
        };
        Constants {
            inner,
            source_text,
            position,
        }
    }
}

// identifier = @{ !(reserved) ~ ASCII_ALPHA ~ (ASCII_ALPHANUMERIC)* }
pub fn parse_identifier(pair: pest::iterators::Pair<Rule>) -> Arc<str> {
    match pair.as_rule() {
        Rule::identifier => Arc::from(pair.as_str()),
        x => {
            unreachable!("expected identifier found {:?}", x);
        }
    }
}

/// Parse a jet name
pub fn parse_func_name(pair: pest::iterators::Pair<Rule>) -> FuncType {
    match pair.as_rule() {
        Rule::jet => FuncType::Jet(Arc::from(pair.as_str().strip_prefix("jet_").unwrap())),
        Rule::builtin => {
            FuncType::BuiltIn(Arc::from(pair.as_str().strip_prefix("builtin_").unwrap()))
        }
        Rule::assertl => FuncType::AssertL,
        Rule::assertr => FuncType::AssertR,
        x => {
            panic!("expected function name found {:?}", x);
        }
    }
}

/// Parse a witness ident
pub fn parse_witness(pair: pest::iterators::Pair<Rule>) -> Arc<str> {
    match pair.as_rule() {
        Rule::witness => Arc::from(pair.as_str().strip_prefix("wit_").unwrap()),
        x => {
            panic!("expected witness found: {:?}", x);
        }
    }
}
