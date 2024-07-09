/// Library for parsing and compiling simfony

pub type ProgNode = Arc<named::NamedConstructNode>;

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

use std::{path::Path, sync::Arc};

use named::ConstructExt;
use simplicity::{dag::NoSharing, jet::Elements, node::Redeem, CommitNode, RedeemNode};

pub extern crate simplicity;
pub use simplicity::elements;
use simplicity::node::SimpleFinalizer;

use crate::{error::WithFile, named::NamedExt};

pub fn compile(file: &Path) -> Result<Arc<CommitNode<Elements>>, String> {
    let file = Arc::<str>::from(std::fs::read_to_string(file).unwrap());
    let parse_program = parse::Program::parse(file.clone())?;
    let ast_program = ast::Program::analyze(&parse_program).with_file(file.clone())?;
    let simplicity_named_construct = ast_program.compile().with_file(file.clone())?;
    let simplicity_named_commit = simplicity_named_construct
        .finalize_types_main()
        .expect("Failed to set program source and target type to unit");
    Ok(simplicity_named_commit.to_commit_node())
}

pub fn satisfy(prog: &Path) -> Result<Arc<RedeemNode<Elements>>, String> {
    let simplicity_named_commit = compile(prog)?;
    let mut finalizer = SimpleFinalizer::new(std::iter::empty());
    simplicity_named_commit
        .convert::<NoSharing, Redeem<Elements>, _>(&mut finalizer)
        .map_err(|_| {
            "Witness expressions are temporarily not supported. Cannot satisfy.".to_string()
        })
}

#[cfg(test)]
mod tests {
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use simplicity::{encode, BitMachine, BitWriter};

    use crate::*;

    #[test]
    fn test_progs() {
        _test_progs("./example_progs/add.simf");
        _test_progs("./example_progs/array.simf");
        // _test_progs("./example_progs/cat.simf");
        _test_progs("./example_progs/checksigfromstackverify.simf");
        _test_progs("./example_progs/ctv.simf");
        _test_progs("./example_progs/list.simf");
        _test_progs("./example_progs/match.simf");
        _test_progs("./example_progs/nesting.simf");
        _test_progs("./example_progs/recursive-covenant.simf");
        _test_progs("./example_progs/scopes.simf");
        _test_progs("./example_progs/sighash_all.simf");
        _test_progs("./example_progs/sighash_all_anyprevoutanyscript.simf");
        _test_progs("./example_progs/sighash_none.simf");
        _test_progs("./example_progs/tuple.simf");
        _test_progs("./example_progs/unwrap.simf");
    }

    fn _test_progs(file: &str) {
        println!("Testing {file}");
        let file = Path::new(file);
        let redeem_prog = match satisfy(file) {
            Ok(commit) => commit,
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
