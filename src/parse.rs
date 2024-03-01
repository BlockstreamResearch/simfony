//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
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

/// Pattern for binding values to variables.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Bind value to variable name.
    Identifier(Arc<str>),
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
            Some(Type::parse(inner_pair.next().unwrap()))
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

impl PestParse for Pattern {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Self {
        assert!(matches!(pair.as_rule(), Rule::pattern));
        let pair = PatternPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::pattern => {}
                Rule::variable_pattern => {
                    let identifier = data.node.0.as_str();
                    output.push(Pattern::Identifier(Arc::from(identifier)));
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
