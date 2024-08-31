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
pub mod str;
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

/// Recursively implement [`PartialEq`], [`Eq`] and [`std::hash::Hash`]
/// using selected members of a given type. The type must have a getter
/// method for each selected member.
#[macro_export]
macro_rules! impl_eq_hash {
    ($ty: ident; $($member: ident),*) => {
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                true $(&& self.$member() == other.$member())*
            }
        }

        impl Eq for $ty {}

        impl std::hash::Hash for $ty {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                $(self.$member().hash(state);)*
            }
        }
    };
}

/// Helper trait for implementing [`arbitrary::Arbitrary`] for recursive structures.
///
/// [`ArbitraryRec::arbitrary_rec`] allows the caller to set a budget that is decreased every time
/// the generated structure gets deeper. The maximum depth of the generated structure is equal to
/// the initial budget. The budget prevents the generated structure from becoming too deep, which
/// could cause issues in the code that processes these structures.
///
/// https://github.com/rust-fuzz/arbitrary/issues/78
#[cfg(feature = "arbitrary")]
trait ArbitraryRec: Sized {
    /// Generate a recursive structure from unstructured data.
    ///
    /// Generate leaves or parents when the budget is positive.
    /// Generate only leaves when the budget is zero.
    ///
    /// ## Implementation
    ///
    /// Recursive calls of [`arbitrary_rec`] must decrease the budget by one.
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self>;
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
            ("cat.simf", "empty.wit"),
            (
                "checksigfromstackverify.simf",
                "checksigfromstackverify.wit",
            ),
            ("ctv.simf", "empty.wit"),
            ("hash_loop.simf", "empty.wit"),
            ("recursive-covenant.simf", "empty.wit"),
            (
                "sighash_all_anyprevoutanyscript.simf",
                "sighash_all_anyprevoutanyscript.wit",
            ),
            ("sighash_none.simf", "sighash_none.wit"),
        ] {
            _test_progs(prog_file, wit_file)
        }
    }

    fn _test_progs(prog_file: &str, wit_file: &str) {
        println!("Testing {prog_file}");
        let parent_path = PathBuf::from("./examples");
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

        assert_success(&prog_text, &witness);
    }

    fn assert_success(prog_text: &str, witness: &WitnessValues) {
        let redeem_prog = match satisfy(prog_text, witness) {
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

        let mut mac = BitMachine::for_program(&redeem_prog);
        let env = dummy_env::dummy();
        mac.exec(&redeem_prog, &env)
            .expect("Machine execution failure");
    }

    fn assert_success_empty_witness(prog_text: &str) {
        let witness = WitnessValues::empty();
        assert_success(prog_text, &witness)
    }

    fn assert_satisfy_error_empty_witness(prog_text: &str, expected_error: &str) {
        let witness = WitnessValues::empty();
        match satisfy(prog_text, &witness) {
            Ok(_) => panic!("Accepted faulty program"),
            Err(error) => {
                if !error.contains(expected_error) {
                    panic!("Unexpected error: {error}")
                }
            }
        }
    }

    #[test]
    fn redefined_variable() {
        let prog_text = r#"fn main() {
    let beefbabe: (u16, u16) = (0xbeef, 0xbabe);
    let beefbabe: u32 = <(u16, u16)>::into(beefbabe);
}
"#;
        assert_success_empty_witness(prog_text);
    }

    #[test]
    fn empty_function_body_nonempty_return() {
        let prog_text = r#"fn my_true() -> bool {
    // function body is empty, although function must return `bool`
}

fn main() {
    jet_verify(my_true());
}
"#;
        assert_satisfy_error_empty_witness(
            prog_text,
            "Expected expression of type `bool`, found type `()`",
        );
    }

    #[test]
    fn fuzz_regression_1() {
        compile("type f=f").unwrap_err();
    }

    #[test]
    #[ignore]
    fn fuzz_slow_unit_1() {
        compile("fn fnnfn(MMet:(((sssss,((((((sssss,ssssss,ss,((((((sssss,ss,((((((sssss,ssssss,ss,((((((sssss,ssssss,((((((sssss,sssssssss,(((((((sssss,sssssssss,(((((ssss,((((((sssss,sssssssss,(((((((sssss,ssss,((((((sssss,ss,((((((sssss,ssssss,ss,((((((sssss,ssssss,((((((sssss,sssssssss,(((((((sssss,sssssssss,(((((ssss,((((((sssss,sssssssss,(((((((sssss,sssssssssssss,(((((((((((u|(").unwrap_err();
    }
}
