extern crate pest;
#[macro_use]
extern crate pest_derive;

use std::{collections::HashMap, hash::Hash};

use pest::{pratt_parser::PrattParser, Parser};

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
            .op(Op::infix(Rule::equals132, Left))
    };
}

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
    dbg!(&prog);
}

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Assert(Assert),
    Assignment(Assignment),
    FuncCall(FuncCall),
}

fn parse_stmt(pair: pest::iterators::Pair<Rule>) -> Statement {
    let inner_pair = pair.into_inner().next().unwrap();
    match inner_pair.as_rule() {
        Rule::assert => Statement::Assert(parse_assert(inner_pair)),
        Rule::assignment => Statement::Assignment(parse_assignment(inner_pair)),
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
    pub expression: Expression,
}

// assignment = { "let" ~ identifier ~ "=" ~ expression }
fn parse_assignment(pair: pest::iterators::Pair<Rule>) -> Assignment {
    let mut inner_pair = pair.into_inner();
    let ident = inner_pair.next().unwrap().as_str();
    let expression = parse_expression(inner_pair.next().unwrap());
    Assignment {
        identifier: ident.to_string(),
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
        Rule::jet => FuncCallType::Jet(func_name_pair.as_str().to_string()),
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
    Term(Box<Term>),
    BinOp {
        lhs: Box<Expression>,
        op: Operator,
        rhs: Box<Expression>,
    },
}

#[derive(Debug)]
pub enum Operator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equals,
}

// expression = { term ~ (operator ~ term)* }
fn parse_expression(pair: pest::iterators::Pair<Rule>) -> Expression {
    let pairs = pair.into_inner();
    dbg!(&pairs);
    PRATT_PARSER
        .map_primary(|term_pair| Expression::Term(Box::new(parse_term(term_pair))))
        .map_infix(|lhs, op, rhs| {
            dbg!(&op);
            let op = parse_operator(op);
            Expression::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
        })
        .parse(pairs)
}

// operator = { "+" | "-" | "*" | "/" }
fn parse_operator(pair: pest::iterators::Pair<Rule>) -> Operator {
    match pair.into_inner().next().unwrap().as_rule() {
        Rule::add => Operator::Add,
        Rule::subtract => Operator::Subtract,
        Rule::multiply => Operator::Multiply,
        Rule::divide => Operator::Divide,
        Rule::equals132 => Operator::Equals,
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
        Rule::identifier | Rule::jet | Rule::witness => pair.as_str().to_string(),
        x => {
            panic!("{:?}", x);
        }
    }
}
