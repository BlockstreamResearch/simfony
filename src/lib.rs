/// Library for parsing and compiling simfony

pub type ProgNode = Arc<named::ConstructNode>;

mod array;
pub mod ast;
pub mod compile;
pub mod dummy_env;
pub mod error;
pub mod jet;
pub mod named;
pub mod num;
pub mod parse;
pub mod pattern;
pub mod types;
pub mod value;
pub mod witness;

use std::sync::Arc;

use simplicity::{jet::Elements, CommitNode, RedeemNode};

pub extern crate simplicity;
pub use simplicity::elements;

use crate::error::WithFile;
use crate::parse::ParseFromStr;
use crate::witness::WitnessValues;

pub fn compile(prog_text: &str) -> Result<Arc<CommitNode<Elements>>, String> {
    let parse_program = parse::Program::parse_from_str(prog_text)?;
    let ast_program = ast::Program::analyze(&parse_program).with_file(prog_text)?;
    let simplicity_named_construct = ast_program.compile().with_file(prog_text)?;
    let simplicity_commit = named::to_commit_node(&simplicity_named_construct)
        .expect("Failed to set program source and target type to unit");
    Ok(simplicity_commit)
}

pub fn satisfy(
    prog_text: &str,
    witness: &WitnessValues,
) -> Result<Arc<RedeemNode<Elements>>, String> {
    let parse_program = parse::Program::parse_from_str(prog_text)?;
    let ast_program = ast::Program::analyze(&parse_program).with_file(prog_text)?;
    let simplicity_named_construct = ast_program.compile().with_file(prog_text)?;
    witness
        .is_consistent(&ast_program)
        .map_err(|e| e.to_string())?;

    let simplicity_witness = named::to_witness_node(&simplicity_named_construct, witness);
    simplicity_witness.finalize().map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use simplicity::{encode, BitMachine, BitWriter};
    use std::path::PathBuf;

    use crate::*;

    #[test]
    fn test_progs() {
        for (prog_file, wit_file) in [
            ("add.simf", "empty.wit"),
            ("add.simf", "empty.wit"),
            ("array.simf", "empty.wit"),
            // ("cat.simf", "empty.wit"),
            (
                "checksigfromstackverify.simf",
                "checksigfromstackverify.wit",
            ),
            ("ctv.simf", "empty.wit"),
            ("list.simf", "empty.wit"),
            ("match.simf", "empty.wit"),
            ("nesting.simf", "empty.wit"),
            ("recursive-covenant.simf", "empty.wit"),
            ("scopes.simf", "empty.wit"),
            ("sighash_all.simf", "empty.wit"),
            (
                "sighash_all_anyprevoutanyscript.simf",
                "sighash_all_anyprevoutanyscript.wit",
            ),
            ("sighash_none.simf", "sighash_none.wit"),
            ("tuple.simf", "empty.wit"),
            ("unwrap.simf", "empty.wit"),
            ("function.simf", "empty.wit"),
        ] {
            _test_progs(prog_file, wit_file)
        }
    }

    fn _test_progs(prog_file: &str, wit_file: &str) {
        println!("Testing {prog_file}");
        let parent_path = PathBuf::from("./example_progs");
        let mut prog_path = parent_path.clone();
        prog_path.push(prog_file);
        let mut wit_path = parent_path;
        wit_path.push(wit_file);

        let prog_text = std::fs::read_to_string(prog_path).unwrap();
        let wit_text = std::fs::read_to_string(wit_path).unwrap();
        let witness = match serde_json::from_str::<WitnessValues>(&wit_text) {
            Ok(x) => x,
            Err(error) => {
                panic!("{error}")
            }
        };
        let redeem_prog = match satisfy(&prog_text, &witness) {
            Ok(x) => x,
            Err(error) => {
                panic!("{error}");
            }
        };

        let mut vec = Vec::new();
        let mut writer = BitWriter::new(&mut vec);
        let _encoded = encode::encode_program(&redeem_prog, &mut writer).unwrap();
        dbg!(&redeem_prog);
        println!("{}", Base64Display::new(&vec, &STANDARD));

        let mut bit_mac = BitMachine::for_program(&redeem_prog);
        let env = dummy_env::dummy();
        bit_mac
            .exec(&redeem_prog, &env)
            .expect("Machine execution failure");
    }
}
