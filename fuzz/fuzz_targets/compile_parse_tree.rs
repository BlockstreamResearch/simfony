#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

use simfony::error::WithFile;
use simfony::{ast, named, parse, ArbitraryOfType, Arguments};

fuzz_target!(|data: &[u8]| {
    let mut u = arbitrary::Unstructured::new(data);
    let parse_program = match parse::Program::arbitrary(&mut u) {
        Ok(x) => x,
        Err(_) => return,
    };
    let ast_program = match ast::Program::analyze(&parse_program) {
        Ok(x) => x,
        Err(_) => return,
    };
    let arguments = match Arguments::arbitrary_of_type(&mut u, ast_program.parameters()) {
        Ok(arguments) => arguments,
        Err(..) => return,
    };
    let simplicity_named_construct = ast_program
        .compile(arguments, false)
        .with_file("")
        .expect("AST should compile with given arguments");
    let _simplicity_commit = named::to_commit_node(&simplicity_named_construct)
        .expect("Conversion to commit node should never fail");
});
