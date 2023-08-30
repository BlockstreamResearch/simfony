use std::sync::Arc;

use pest::Parser;
use simplicity::{encode, node::SimpleFinalizer, BitMachine, BitWriter, Value};

use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;

use simp_lang::{
    dummy_env,
    named::{ConstructExt, NamedExt},
    parse::{PestParse, Program, Statement},
    scope::GlobalScope,
    IdentParser, Rule,
};

fn main() {
    let file = std::fs::read_to_string("./test.txt").unwrap();
    let pairs = IdentParser::parse(Rule::program, &file).unwrap_or_else(|e| panic!("{}", e));

    let mut stmts = Vec::new();
    // Because ident_list is silent, the iterator will contain idents
    for pair in pairs {
        // A pair can be converted to an iterator of the tokens which make it up:
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::statement => stmts.push(Statement::parse(inner_pair)),
                Rule::EOI => println!("EOI:     {}", inner_pair.as_str()),
                _ => unreachable!(),
            };
        }
    }
    let prog = Program { statements: stmts };
    let mut scope = GlobalScope::new();
    let simplicity_prog = prog.eval(&mut scope);
    let mut vec = Vec::new();
    let mut writer = BitWriter::new(&mut vec);
    encode::encode_program(&simplicity_prog, &mut writer).unwrap();
    println!("{}", Base64Display::new(&vec, &STANDARD));
    dbg!(&simplicity_prog);
    let commit_node = simplicity_prog
        .finalize_types_main()
        .expect("Type check error");
    let commit_node = commit_node.to_commit_node();
    let simplicity_prog =
        Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");
    dbg!(&simplicity_prog);
    let encoded = simplicity_prog.encode_to_vec();
    println!("{}", Base64Display::new(&encoded, &STANDARD));
    let v: Vec<Arc<Value>> = vec![];
    let mut finalizer = SimpleFinalizer::new(v.into_iter());
    let redeem_prog = simplicity_prog.finalize(&mut finalizer).unwrap();
    let mut bit_mac = BitMachine::for_program(&redeem_prog);
    let env = dummy_env::dummy();
    bit_mac
        .exec(&redeem_prog, &env)
        .expect("Machine execution failure");
}
