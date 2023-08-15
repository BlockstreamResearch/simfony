extern crate pest;
#[macro_use]
extern crate pest_derive;

use core::fmt;
use std::{collections::HashMap, hash::Hash, str::FromStr, sync::Arc, vec};

use pest::{pratt_parser::PrattParser, Parser};
use simplicity::{
    hex::{self, FromHex},
    jet::{Elements, Jet, elements::ElementsEnv},
    node::{self, Construct, CoreConstructible, JetConstructible, WitnessConstructible, SimpleFinalizer},
    types, CommitNode, ConstructNode, Value, BitMachine, RedeemNode, BitWriter,
};

use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;

#[derive(Parser)]
#[grammar = "test.pest"]
struct IdentParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};

        PrattParser::new()
        // Addition and subtract have equal precedence
            .op(Op::infix(Rule::add, Left) | Op::infix(Rule::subtract, Left))
            .op(Op::infix(Rule::multiply, Left) | Op::infix(Rule::divide, Left))
            .op(Op::infix(Rule::equals, Left))
    };
}

type ProgNode = Arc<ConstructNode<Elements>>;

mod scope {
    use super::*;

    #[derive(Debug)]
    pub struct GlobalScope {
        variables: Vec<Vec<String>>,
    }

    impl GlobalScope {
        pub fn new() -> Self {
            GlobalScope {
                variables: vec![Vec::new()],
            }
        }

        pub fn push_scope(&mut self) {
            self.variables.push(Vec::new());
        }

        pub fn pop_scope(&mut self) {
            self.variables.pop().expect("Popping scope zero");
        }

        pub fn push(&mut self, key: String) {
            self.variables.last_mut().unwrap().push(key);
            dbg!(&self);
        }

        pub fn get(&self, key: &str) -> ProgNode {
            // search in the vector of vectors from the end
            let mut pos = 0;
            let mut found = false;
            for v in self.variables.iter().rev() {
                if let Some(idx) = v.iter().rev().position(|var_name| var_name == key) {
                    pos += idx;
                    found = true;
                    break;
                } else {
                    pos += v.len();
                }
            }
            if !found {
                panic!("Variable {} not found", key);
            }
            let mut child = ProgNode::iden();
            child = ProgNode::drop_(&child);
            for _ in 0..pos {
                child = ProgNode::take(&child);
            }
            println!("Fetching for variable {key} as {pos}, {child:?}");
            child
        }
    }
}

use scope::GlobalScope;

use crate::dummy_env::dummy;

fn main() {
    let file = std::fs::read_to_string("./test.txt").unwrap();
    let pairs = IdentParser::parse(Rule::program, &file).unwrap_or_else(|e| panic!("{}", e));

    let mut stmts = Vec::new();
    // Because ident_list is silent, the iterator will contain idents
    for pair in pairs {
        dbg!(&pair);
        // A pair is a combination of the rule which matched and a span of input
        println!("Rule:    {:?}", pair.as_rule());
        println!("Span:    {:?}", pair.as_span());
        println!("Text:    {}", pair.as_str());

        // A pair can be converted to an iterator of the tokens which make it up:
        for inner_pair in pair.into_inner() {
            // dbg!(&inner_pair);
            match inner_pair.as_rule() {
                Rule::statement => stmts.push(parse_stmt(inner_pair)),
                Rule::EOI => println!("EOI:     {}", inner_pair.as_str()),
                // Rule::digit => println!("Digit:   {}", inner_pair.as_str()),
                _ => unreachable!(),
            };
        }
    }
    let prog = Program { statements: stmts };
    let mut scope = GlobalScope::new();
    let simplicity_prog = prog.eval(0, &mut scope);
    let mut vec = Vec::new();
    let mut writer = BitWriter::new(&mut vec);
    simplicity_prog.encode(&mut writer).unwrap();
    println!("{}", Base64Display::new(&vec, &STANDARD));
    dbg!(&simplicity_prog);
    let commit_node = simplicity_prog.finalize_types().expect("Type check error");
    let simplicity_prog =
        Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");
    dbg!(&simplicity_prog);
    let encoded = simplicity_prog.encode_to_vec();
    println!("{}", Base64Display::new(&encoded, &STANDARD));
    let v : Vec<Arc<Value>> = vec![];
    let mut finalizer = SimpleFinalizer::new(v.into_iter());
    let redeem_prog = simplicity_prog.finalize(&mut finalizer).unwrap();
    let mut bit_mac = BitMachine::for_program(&redeem_prog);
    let env = dummy_env::dummy();
    bit_mac.exec(&redeem_prog, &env).expect("Machine execution failure");
}

fn eval_blk(stmts: &[Statement], scope: &mut GlobalScope, index: usize, last_expr: Option<&Box<Expression>>) -> ProgNode {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.eval(scope, None),
            None => ProgNode::unit(),
        }
    }
    let res = match &stmts[index] {
        Statement::Assert(assert) => {
            let expr = assert.expression.eval(scope, None);
            let jet = ProgNode::jet(Elements::Verify);
            ProgNode::comp(&expr, &jet).expect("Improve this error. asserts must be a bool")
        }
        Statement::Assignment(assignment) => {
            let expr = assignment.expression.eval(scope, assignment.ty);
            scope.push(assignment.identifier.clone());
            let left =
                ProgNode::pair(&ProgNode::iden(), &expr).expect("TYPECHECK: must succeed.");
            let right = eval_blk(stmts, scope, index + 1, last_expr);
            println!("l:{} r:{} index:{index}", &left.arrow(), &right.arrow());
            ProgNode::comp(&left, &right).expect(&format!(
                "Improve this error. assignments must be of unit target type {index}"
            ))
        }
        Statement::WitnessDecl(witness_ident) => {
            let witness = ProgNode::witness(node::NoWitness);
            todo!();
            // scope.insert(witness_ident.to_string());
            // continue;
        }
        Statement::FuncCall(func_call) => {
            let left = func_call.eval(scope, None);
            let right = eval_blk(stmts, scope, index + 1, last_expr);
            combine_seq(&left, &right)
        }
    };
    dbg!(res)
}

fn combine_seq(a: &ProgNode, b: &ProgNode) -> ProgNode {
    let pair = ProgNode::pair(a, b).expect("Pair creation error");
    let drop_iden = ProgNode::drop_(&ProgNode::iden());
    ProgNode::comp(&pair, &drop_iden).expect("Improve this error. func calls must be of unit target type")
}

impl Program {
    fn eval(&self, index: usize, scope: &mut GlobalScope) -> ProgNode {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl FuncCall {
    fn eval(&self, scope: &mut GlobalScope, _reqd_ty: Option<Type>) -> ProgNode {
        let args = self
            .args
            .iter()
            .map(|e| e.eval(scope, None)) // TODO: Pass the jet source type here.
            .reduce(|acc, e| ProgNode::pair(&acc, &e).expect("Function arg creation error"));
        let jet_name = match &self.func_name {
            FuncCallType::Jet(name) => name,
            FuncCallType::UserCall(_name) => panic!("User calls not implemented"),
        };
        println!("Jet name: {}", jet_name);
        let res = match args {
            Some(param) => {
                let jet = Elements::from_str(jet_name).expect("Invalid jet name");
                let jet = ProgNode::jet(jet);
                ProgNode::comp(&param, &jet)
                    .expect("Improve this error. func calls must have correct arguments")
            }
            None => {
                let jet = Elements::from_str(jet_name).expect("Invalid jet name");
                ProgNode::jet(jet)
            }
        };
        res
    }
}

impl Expression {

    fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<Type>) -> ProgNode {
        match self {
            Expression::BlockExpression(stmts, expr) => {
                scope.push_scope();
                let res = eval_blk(stmts, scope, 0, Some(expr));
                scope.pop_scope();
                res
            },
            Expression::Pair(e1, e2) => {
                ProgNode::pair(&e1.eval(scope, None), &e2.eval(scope, None)).expect("Pair error")
            },
            Expression::SingleExpression(e) => {
                e.eval(scope, reqd_ty)
            },
        }
    }
}

impl SingleExpression {
    fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<Type>) -> ProgNode {
        let res = match self {
            SingleExpression::Term(term) => term.eval(scope, reqd_ty),
            SingleExpression::BinOp { lhs, op, rhs } => {
                let lhs = lhs.eval(scope, reqd_ty);
                let rhs = rhs.eval(scope, reqd_ty);
                // Create a pair of nodes
                let inp = ProgNode::pair(&lhs, &rhs).expect(&format!(
                    "Pair creation failed. \n
                        The operators of {:?} must be of the same type. \n
                        Left type: {:?} \n
                        Right type: {:?} \n",
                    op,
                    lhs.arrow().target,
                    rhs.arrow().target
                ));
                match op {
                    Operator::Add => {
                        let add = ProgNode::jet(Elements::Add32);
                        ProgNode::comp(&inp, &add)
                            .expect("Improve this error. adds must be 32 bits")
                    }
                    // Operator::Subtract => node!(lhs - rhs),
                    // Operator::Multiply => node!(lhs * rhs),
                    // Operator::Divide => node!(lhs / rhs),
                    Operator::Equals => {
                        let equals = ProgNode::jet(Elements::Eq32);
                        ProgNode::comp(&inp, &equals)
                            .expect("Improve this error. equals must be a bool")
                    }
                    _ => todo!(),
                }
            }
        };
        if let Some(reqd_ty) = reqd_ty {
            res.arrow()
                .target
                .unify(
                    &reqd_ty.to_simplicity_type(),
                    "Type mismatch for user provided type",
                )
                .unwrap();
        }
        res
    }
}

fn assert_type(reqd_ty: Option<Type>, actual_ty: Type) {
    if let Some(reqd_ty) = reqd_ty {
        if reqd_ty != actual_ty {
            panic!(
                "Type mismatch. Expected {:?} but got {:?}",
                reqd_ty, actual_ty
            );
        }
    }
}

impl Term {
    fn eval(&self, scope: &mut GlobalScope, reqd_ty: Option<Type>) -> ProgNode {
        let res = match self {
            Term::Constants(constants) => match constants {
                Constants::None => todo!("None type here"),
                Constants::False => {
                    let _false = Arc::new(Value::u1(0));
                    assert_type(reqd_ty, Type::U1);
                    ProgNode::const_word(_false)
                }
                Constants::True => {
                    let _true = Arc::new(Value::u1(1));
                    assert_type(reqd_ty, Type::U1);
                    ProgNode::const_word(_true)
                }
                Constants::Number(number) => {
                    let v = if let Some(ty) = reqd_ty {
                        ty.parse_num(number)
                    } else {
                        let num = number.parse::<u32>().unwrap();
                        Value::u32(num)
                    };
                    ProgNode::comp(&ProgNode::unit(), &ProgNode::const_word(Arc::new(v)))
                        .expect("Const word have source type one")
                }
                Constants::Str(str) => todo!("TODO: figure out string type here"),
            },
            Term::Jet(jet) => {
                let jet = Elements::from_str(jet).expect("Invalid jet name");
                // assert_type(reqd_ty, jet.target_ty());
                ProgNode::jet(jet)
            }
            Term::Witness(witness) => ProgNode::witness(node::NoWitness),
            Term::FuncCall(func_call) => func_call.eval(scope, reqd_ty),
            Term::Identifier(identifier) => scope.get(identifier),
            Term::Expression(expression) => expression.eval(scope, reqd_ty),
        };
        if let Some(reqd_ty) = reqd_ty {
            res.arrow()
                .target
                .unify(
                    &reqd_ty.to_simplicity_type(),
                    "Type mismatch for user provided type",
                )
                .unwrap();
        }
        res
    }
}

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Assert(Assert),
    Assignment(Assignment),
    WitnessDecl(String),
    FuncCall(FuncCall),
}

fn parse_stmt(pair: pest::iterators::Pair<Rule>) -> Statement {
    let inner_pair = pair.into_inner().next().unwrap();
    match inner_pair.as_rule() {
        Rule::assert => Statement::Assert(parse_assert(inner_pair)),
        Rule::assignment => Statement::Assignment(parse_assignment(inner_pair)),
        Rule::witness_decl => Statement::WitnessDecl(parse_identifier(inner_pair)),
        // Rule::expression => println!("Expression:  {}", inner_pair.as_str()),
        Rule::func_call => Statement::FuncCall(parse_func_call(inner_pair)),
        // Rule::digit => println!("Digit:   {}", inner_pair.as_str()),
        x => {
            panic!("{:?}", x);
        }
    }
}

#[derive(Debug)]
pub struct Assert {
    pub expression: Expression,
}

// assert = { "assert" ~ "(" ~ expression ~ ")" }
fn parse_assert(pair: pest::iterators::Pair<Rule>) -> Assert {
    let inner_pair = pair.into_inner().next().unwrap();
    match inner_pair.as_rule() {
        Rule::expression => Assert {
            expression: parse_expression(inner_pair),
        },
        x => {
            panic!("{:?}", x);
        }
    }
}

#[derive(Debug)]
pub struct Assignment {
    pub identifier: String,
    pub ty: Option<Type>,
    pub expression: Expression,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
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
    /// For the supported operations with the expected output type.
    /// Return the corresponding jet to use and expected type for the input.
    ///
    /// For example, for the operation `let c : u32 = a + b`. Impose the constraint
    /// that `a` and `b` must be of type `u32` and jet the use is `add32`.
    fn jet_and_operand_type(&self, op: Operator) -> (Elements, Type) {
        match (self, op) {
            (Type::U8, Operator::Add) => (Elements::Add8, Type::U8),
            (Type::U8, Operator::Subtract) => (Elements::Subtract8, Type::U8),
            (Type::U8, Operator::Multiply) => (Elements::Multiply8, Type::U8),
            (Type::U8, Operator::Divide) => (Elements::Divide8, Type::U8),
            (Type::U8, Operator::Equals) => panic!("Equals must output a bool"),
            (Type::U16, Operator::Add) => (Elements::Add16, Type::U16),
            (Type::U16, Operator::Subtract) => (Elements::Subtract16, Type::U16),
            (Type::U16, Operator::Multiply) => (Elements::Multiply16, Type::U16),
            (Type::U16, Operator::Divide) => (Elements::Divide16, Type::U16),
            (Type::U16, Operator::Equals) => panic!("Equals must output a bool"),
            (Type::U32, Operator::Add) => (Elements::Add32, Type::U32),
            (Type::U32, Operator::Subtract) => (Elements::Subtract32, Type::U32),
            (Type::U32, Operator::Multiply) => (Elements::Multiply32, Type::U32),
            (Type::U32, Operator::Divide) => (Elements::Divide32, Type::U32),
            (Type::U32, Operator::Equals) => panic!("Equals must output a bool"),
            (Type::U64, Operator::Add) => (Elements::Add64, Type::U64),
            (Type::U64, Operator::Subtract) => (Elements::Subtract64, Type::U64),
            (Type::U64, Operator::Multiply) => (Elements::Multiply64, Type::U64),
            (Type::U64, Operator::Divide) => (Elements::Divide64, Type::U64),
            (Type::U64, Operator::Equals) => panic!("Equals must output a bool"),
            (Type::Pubkey, Operator::Add) => panic!("Addition cannot output pubkey"),
            (Type::Pubkey, Operator::Subtract) => panic!("Subtraction cannot output pubkey"),
            (Type::Pubkey, Operator::Multiply) => panic!("Multiplication cannot output pubkey"),
            (Type::Pubkey, Operator::Divide) => panic!("Division cannot output pubkey"),
            (Type::Pubkey, Operator::Equals) => panic!("Equals must output a bool"),
            _ => panic!("Invalid operation for type {} with operator {:?}", self, op),
        }
    }

    /// Parse a number from a string for the given type
    /// and return the corresponding value.
    fn parse_num(&self, s: &str) -> Value {
        match self {
            Type::U8 => Value::u8(s.parse::<u8>().unwrap()),
            Type::U16 => Value::u16(s.parse::<u16>().unwrap()),
            Type::U32 => Value::u32(s.parse::<u32>().unwrap()),
            Type::U64 => Value::u64(s.parse::<u64>().unwrap()),
            Type::Pubkey | Type::U256 => {
                let hex_decoded = Vec::<u8>::from_hex(&s[2..]).unwrap();
                Value::u256_from_slice(&hex_decoded)
            }
            _ => panic!("Invalid type for number parsing"),
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

// assignment = { "let" ~ identifier ~ "=" ~ expression }
fn parse_assignment(pair: pest::iterators::Pair<Rule>) -> Assignment {
    let mut inner_pair = pair.into_inner();
    let ident = inner_pair.next().unwrap().as_str();
    let reqd_ty = if let Rule::ty = inner_pair.peek().unwrap().as_rule() {
        let ty = inner_pair.next().unwrap().as_str().parse::<Type>().unwrap();
        Some(ty)
    } else {
        None
    };
    let expression = parse_expression(inner_pair.next().unwrap());
    Assignment {
        identifier: ident.to_string(),
        ty: reqd_ty,
        expression,
    }
}

#[derive(Debug)]
pub struct FuncCall {
    pub func_name: FuncCallType,
    pub args: Vec<Expression>,
}

#[derive(Debug)]
pub enum FuncCallType {
    Jet(String),
    UserCall(String),
}

// func_call = { func_name ~ "(" ~ (expression ~ ("," ~ expression)*)? ~ ")" }
fn parse_func_call(pair: pest::iterators::Pair<Rule>) -> FuncCall {
    let mut pair = pair.into_inner();
    let func_name_pair = pair.next().unwrap();
    let func_name = match func_name_pair.as_rule() {
        Rule::jet => FuncCallType::Jet(
            func_name_pair
                .as_str()
                .strip_prefix("jet_")
                .unwrap()
                .to_string(),
        ),
        Rule::identifier => FuncCallType::UserCall(func_name_pair.as_str().to_string()),
        x => {
            panic!("{:?}", x);
        }
    };
    let mut args = Vec::new();
    for inner_pair in pair {
        match inner_pair.as_rule() {
            Rule::expression => args.push(parse_expression(inner_pair)),
            x => {
                panic!("{:?}", x);
            }
        };
    }
    FuncCall {
        func_name: func_name,
        args,
    }
}

// expression = { term ~ (operator ~ term)* }
#[derive(Debug)]
pub enum Expression {
    BlockExpression(Vec<Statement>, Box<Expression>),
    Pair(Box<Expression>, Box<Expression>),
    SingleExpression(Box<SingleExpression>)
}

// single_expression = { term ~ (operator ~ term)* }
#[derive(Debug)]
pub enum SingleExpression {
    Term(Box<Term>),
    BinOp {
        lhs: Box<SingleExpression>,
        op: Operator,
        rhs: Box<SingleExpression>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Operator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equals,
}

// expression = { block_expression |pair | term ~ (operator ~ term)* }
fn parse_expression(pair: pest::iterators::Pair<Rule>) -> Expression {
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::block_expression => {
            let mut stmts = Vec::new();
            let mut inner_pair = pair.into_inner();
            while let Some(Rule::statement) = inner_pair.peek().map(|x| x.as_rule()) {
                stmts.push(parse_stmt(inner_pair.next().unwrap()));
            }
            let expr = parse_expression(inner_pair.next().unwrap());
            Expression::BlockExpression(stmts, Box::new(expr))
        }
        Rule::pair => {
            let mut inner_pair = pair.into_inner();
            let lhs = parse_expression(inner_pair.next().unwrap());
            let rhs = parse_expression(inner_pair.next().unwrap());
            Expression::Pair(Box::new(lhs), Box::new(rhs))
        }
        Rule::single_expression => Expression::SingleExpression(Box::new(parse_single_expression(pair))),
        x => {
            panic!("{:?}", x);
        }
    }
}

// expression = { term ~ (operator ~ term)* }
fn parse_single_expression(pair: pest::iterators::Pair<Rule>) -> SingleExpression {
    let pairs = pair.into_inner();
    dbg!(&pairs);
    PRATT_PARSER
        .map_primary(|term_pair| dbg!(SingleExpression::Term(Box::new(parse_term(term_pair)))))
        .map_infix(|lhs, op, rhs| {
            dbg!(&op);
            let op = parse_operator(op);
            SingleExpression::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
        })
        .parse(pairs)
}

// operator = { "+" | "-" | "*" | "/" }
fn parse_operator(pair: pest::iterators::Pair<Rule>) -> Operator {
    match pair.as_rule() {
        Rule::add => Operator::Add,
        Rule::subtract => Operator::Subtract,
        Rule::multiply => Operator::Multiply,
        Rule::divide => Operator::Divide,
        Rule::equals => Operator::Equals,
        x => {
            panic!("{:?}", x);
        }
    }
}

#[derive(Debug)]
pub enum Term {
    Constants(Constants),
    Jet(String),
    Witness(String),
    FuncCall(FuncCall),
    Identifier(String),
    Expression(Expression),
}

// term = { constants | jet | witness | func_call | identifier| "(" ~ expression ~ ")"}
fn parse_term(pair: pest::iterators::Pair<Rule>) -> Term {
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::constants => Term::Constants(parse_constants(pair)),
        Rule::jet => Term::Jet(parse_identifier(pair)),
        Rule::witness => Term::Witness(parse_identifier(pair)),
        Rule::func_call => Term::FuncCall(parse_func_call(pair)),
        Rule::identifier => Term::Identifier(parse_identifier(pair)),
        Rule::expression => Term::Expression(parse_expression(pair)),
        x => {
            panic!("{:?} {:?}", x, pair);
        }
    }
}

#[derive(Debug)]
pub enum Constants {
    None,
    False,
    True,
    Number(String),
    Str(String),
}

// constants = { none | false | true | number | str}
fn parse_constants(pair: pest::iterators::Pair<Rule>) -> Constants {
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::none => Constants::None,
        Rule::false_ => Constants::False,
        Rule::true_ => Constants::True,
        Rule::number => Constants::Number(pair.as_str().to_string()),
        Rule::str => Constants::Str(pair.as_str().to_string()),
        x => {
            panic!("{:?}", x);
        }
    }
}

// identifier = @{ !(reserved) ~ ASCII_ALPHA ~ (ASCII_ALPHANUMERIC)* }
pub fn parse_identifier(pair: pest::iterators::Pair<Rule>) -> String {
    match pair.as_rule() {
        Rule::identifier => pair.as_str().to_string(),
        Rule::jet => pair.as_str().strip_prefix("jet_").unwrap().to_string(),
        Rule::witness => pair.as_str().strip_prefix("wit_").unwrap().to_string(),
        Rule::witness_decl => parse_identifier(pair.into_inner().next().unwrap()),
        x => {
            panic!("{:?}", x);
        }
    }
}


mod dummy_env {
    use std::sync::Arc;

    use simplicity::{jet::elements::{ElementsEnv, ElementsUtxo}, elements::{self, confidential, taproot::ControlBlock}, hashes, Cmr};

    /// Return a dummy Elements environment
    pub fn dummy() -> ElementsEnv {
        {
            let lock_time = elements::LockTime::ZERO;let sequence = elements::Sequence::MAX;
            use elements::AssetIssuance;
            use hashes::Hash;

            let ctrl_blk: [u8; 33] = [
                0xc0, 0xeb, 0x04, 0xb6, 0x8e, 0x9a, 0x26, 0xd1, 0x16, 0x04, 0x6c, 0x76, 0xe8, 0xff,
                0x47, 0x33, 0x2f, 0xb7, 0x1d, 0xda, 0x90, 0xff, 0x4b, 0xef, 0x53, 0x70, 0xf2, 0x52,
                0x26, 0xd3, 0xbc, 0x09, 0xfc,
            ];

            ElementsEnv::new(
                Arc::new(elements::Transaction {
                    version: 2,
                    lock_time,
                    // Enable locktime in dummy txin
                    input: vec![elements::TxIn {
                        previous_output: elements::OutPoint::default(),
                        is_pegin: false,
                        script_sig: elements::Script::new(),
                        sequence,
                        asset_issuance: AssetIssuance::default(),
                        witness: elements::TxInWitness::default(),
                    }],
                    output: Vec::default(),
                }),
                vec![ElementsUtxo {
                    script_pubkey: elements::Script::new(),
                    asset: confidential::Asset::Null,
                    value: confidential::Value::Null,
                }],
                0,
                Cmr::from_byte_array([0; 32]),
                ControlBlock::from_slice(&ctrl_blk).unwrap(),
                None,
                elements::BlockHash::all_zeros(),
            )
        }
    }

    /// Return a dummy Elements environment with given locktime
    pub fn dummy_with(lock_time: elements::LockTime, sequence: elements::Sequence) -> ElementsEnv {
        use elements::AssetIssuance;
        use hashes::Hash;

        let ctrl_blk: [u8; 33] = [
            0xc0, 0xeb, 0x04, 0xb6, 0x8e, 0x9a, 0x26, 0xd1, 0x16, 0x04, 0x6c, 0x76, 0xe8, 0xff,
            0x47, 0x33, 0x2f, 0xb7, 0x1d, 0xda, 0x90, 0xff, 0x4b, 0xef, 0x53, 0x70, 0xf2, 0x52,
            0x26, 0xd3, 0xbc, 0x09, 0xfc,
        ];

        ElementsEnv::new(
            Arc::new(elements::Transaction {
                version: 2,
                lock_time,
                // Enable locktime in dummy txin
                input: vec![elements::TxIn {
                    previous_output: elements::OutPoint::default(),
                    is_pegin: false,
                    script_sig: elements::Script::new(),
                    sequence,
                    asset_issuance: AssetIssuance::default(),
                    witness: elements::TxInWitness::default(),
                }],
                output: Vec::default(),
            }),
            vec![ElementsUtxo {
                script_pubkey: elements::Script::new(),
                asset: confidential::Asset::Null,
                value: confidential::Value::Null,
            }],
            0,
            Cmr::from_byte_array([0; 32]),
            ControlBlock::from_slice(&ctrl_blk).unwrap(),
            None,
            elements::BlockHash::all_zeros(),
        )
    }
}