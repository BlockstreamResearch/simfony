#![no_main]

use libfuzzer_sys::fuzz_target;

use simfony::parse::{self, ParseFromStr};

fuzz_target!(|parse_program: parse::Program| {
    let program_text = parse_program.to_string();
    let restored_parse_program = parse::Program::parse_from_str(program_text.as_str())
        .expect("Output of fmt::Display should be parseable");
    assert_eq!(
        parse_program, restored_parse_program,
        "Output of fmt::Display should parse to original program"
    );
});
