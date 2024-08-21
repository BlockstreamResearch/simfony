#![no_main]

use libfuzzer_sys::fuzz_target;

use simfony::error::WithFile;
use simfony::{ast, named, parse};

fuzz_target!(|parse_program: parse::Program| {
    match ast::Program::analyze(&parse_program) {
        Ok(ast_program) => {
            let simplicity_named_construct = ast_program
                .compile()
                .with_file("")
                .expect("AST should always compile");
            let _simplicity_commit = named::to_commit_node(&simplicity_named_construct)
                .expect("Conversion to commit node should never fail");
        }
        Err(_) => {}
    }
});
