/// Library for parsing and compiling s-lang

pub type ProgNode = Arc<named::NamedConstructNode>;

mod array;
pub mod compile;
pub mod dummy_env;
pub mod error;
pub mod named;
pub mod num;
pub mod parse;
pub mod scope;

use std::{collections::HashMap, path::Path, sync::Arc};

use named::{ConstructExt, Named};
use pest::Parser;
use pest_derive::Parser;
use simplicity::{
    dag::{NoSharing, PostOrderIterItem},
    jet::Elements,
    node::{Commit, Converter, Inner, Node, Redeem, RedeemData},
    BitIter, CommitNode, RedeemNode,
};

pub extern crate simplicity;
pub use simplicity::elements;

use crate::{
    error::{RichError, WithFile},
    named::{NamedCommitNode, NamedExt},
    parse::{PestParse, Program},
    scope::GlobalScope,
};

#[derive(Parser)]
#[grammar = "minimal.pest"]
pub struct IdentParser;

pub fn compile_named(program: Arc<str>) -> Result<Arc<Node<Named<Commit<Elements>>>>, String> {
    let simfony_program = IdentParser::parse(Rule::program, &program)
        .map_err(RichError::from)
        .and_then(|mut pairs| Program::parse(pairs.next().unwrap()))
        .with_file(program.clone())?;

    let mut scope = GlobalScope::new();
    let simplicity_program = simfony_program.eval(&mut scope).with_file(program)?;
    let named_commit = simplicity_program
        .finalize_types_main()
        .expect("Type check error");
    Ok(named_commit)
}

pub fn compile(file: Arc<str>) -> Result<CommitNode<Elements>, String> {
    let named_commit = compile_named(file)?;
    Ok(Arc::try_unwrap(named_commit.to_commit_node()).unwrap())
}

pub fn satisfy(program: Arc<str>, wit_file: &Path) -> Result<RedeemNode<Elements>, String> {
    #[derive(serde::Serialize, serde::Deserialize)]
    #[serde(transparent)]
    struct WitFileData {
        map: HashMap<String, String>,
    }

    impl Converter<Named<Commit<Elements>>, Redeem<Elements>> for WitFileData {
        type Error = ();

        fn convert_witness(
            &mut self,
            data: &PostOrderIterItem<&NamedCommitNode>,
            _witness: &<Named<Commit<Elements>> as simplicity::node::Marker>::Witness,
        ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Witness, Self::Error> {
            let key = data.node.name();
            let ty = &data.node.arrow().target;
            match self.map.get(key.as_ref()) {
                Some(wit) => {
                    let bytes: Vec<u8> = hex_conservative::FromHex::from_hex(wit).unwrap();
                    let total_bit_len = bytes.len() * 8;
                    let mut bit_iter = BitIter::new(bytes.into_iter());
                    let value = bit_iter.read_value(&data.node.arrow().target);
                    let v = match value {
                        Ok(v) => v,
                        Err(e) => panic!("Error reading witness: {:?}", e),
                    };
                    // TODO: Make sure that remaining iterator is empty or all zeros till the specified remaining len.
                    let bit_len = ty.bit_width();
                    let remaining = total_bit_len - bit_len;
                    assert!(remaining < 8);
                    for _ in 0..remaining {
                        assert!(!bit_iter.next().unwrap());
                    }
                    assert!(bit_iter.next().is_none());
                    Ok(v)
                }
                None => panic!("Value not found{}", key),
            }
        }

        fn convert_disconnect(
            &mut self,
            _data: &PostOrderIterItem<&NamedCommitNode>,
            _maybe_converted: Option<&Arc<simplicity::node::Node<Redeem<Elements>>>>,
            _disconnect: &<Named<Commit<Elements>> as simplicity::node::Marker>::Disconnect,
        ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Disconnect, Self::Error>
        {
            todo!()
        }

        fn convert_data(
            &mut self,
            data: &PostOrderIterItem<&NamedCommitNode>,
            inner: Inner<
                &Arc<simplicity::node::Node<Redeem<Elements>>>,
                <Redeem<Elements> as simplicity::node::Marker>::Jet,
                &<Redeem<Elements> as simplicity::node::Marker>::Disconnect,
                &<Redeem<Elements> as simplicity::node::Marker>::Witness,
            >,
        ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::CachedData, Self::Error>
        {
            let converted_data = inner
                .map(|node| node.cached_data())
                .map_disconnect(|node| node.cached_data())
                .map_witness(Arc::clone);
            Ok(Arc::new(RedeemData::new(
                data.node.arrow().shallow_clone(),
                converted_data,
            )))
        }
    }

    let commit_node = compile_named(program)?;
    let simplicity_prog =
        Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");

    let file = std::fs::File::open(wit_file).expect("Error opening witness file");
    let rdr = std::io::BufReader::new(file);
    let mut wit_data: WitFileData =
        serde_json::from_reader(rdr).expect("Error reading witness file");

    let redeem_prog = simplicity_prog
        .convert::<NoSharing, Redeem<Elements>, _>(&mut wit_data)
        .unwrap();
    Ok(Arc::try_unwrap(redeem_prog).unwrap())
}

#[cfg(test)]
mod tests {
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use simplicity::{encode, BitMachine, BitWriter, Cmr, Value};

    use crate::{named::ProgExt, *};

    #[test]
    fn test_progs() {
        _test_progs("./example_progs/test.simpl");
        _test_progs("./example_progs/assertr.simpl");
        _test_progs("./example_progs/scopes.simpl");
        _test_progs("./example_progs/nesting.simpl");
        _test_progs("./example_progs/add.simpl");
        _test_progs("./example_progs/cat.simpl");
        _test_progs("./example_progs/match.simpl");
        _test_progs("./example_progs/array.simpl");
        _test_progs("./example_progs/list.simpl");
    }

    fn _test_progs(file: &str) {
        let program_str = Arc::from(std::fs::read_to_string(file).unwrap());
        let simplicity_prog = compile_named(program_str).unwrap();

        struct MyConverter;

        impl Converter<Named<Commit<Elements>>, Redeem<Elements>> for MyConverter {
            type Error = ();

            fn convert_witness(
                &mut self,
                _data: &PostOrderIterItem<&NamedCommitNode>,
                _witness: &<Named<Commit<Elements>> as simplicity::node::Marker>::Witness,
            ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Witness, Self::Error>
            {
                Ok(Value::u32(20))
            }

            fn convert_disconnect(
                &mut self,
                _data: &PostOrderIterItem<&NamedCommitNode>,
                _maybe_converted: Option<&Arc<simplicity::node::Node<Redeem<Elements>>>>,
                _disconnect: &<Named<Commit<Elements>> as simplicity::node::Marker>::Disconnect,
            ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Disconnect, Self::Error>
            {
                todo!()
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&NamedCommitNode>,
                inner: Inner<
                    &Arc<simplicity::node::Node<Redeem<Elements>>>,
                    <Redeem<Elements> as simplicity::node::Marker>::Jet,
                    &<Redeem<Elements> as simplicity::node::Marker>::Disconnect,
                    &<Redeem<Elements> as simplicity::node::Marker>::Witness,
                >,
            ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::CachedData, Self::Error>
            {
                let converted_data = inner
                    .map(|node| node.cached_data())
                    .map_disconnect(|node| node.cached_data())
                    .map_witness(Arc::clone);
                Ok(Arc::new(RedeemData::new(
                    data.node.arrow().shallow_clone(),
                    converted_data,
                )))
            }
        }

        let redeem_prog = simplicity_prog
            .convert::<NoSharing, Redeem<Elements>, _>(&mut MyConverter)
            .unwrap();

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

    #[test]
    fn temp_progs() {
        let inp = ProgNode::const_word(Value::u32(10));
        let node = ProgNode::jet(Elements::ParseLock);
        println!("l1: {}", node.arrow());
        let node = ProgNode::comp(inp, node).unwrap();
        println!("l2: {}", node.arrow());
        let node = ProgNode::pair(node, ProgNode::unit()).unwrap();
        println!("l3: {}", node.arrow());
        let later_operation = ProgNode::take(ProgNode::unit());
        println!("l4: {}", later_operation.arrow());
        let assert_node = ProgNode::assertl(later_operation, Cmr::unit()).unwrap();
        println!("l5: {}", assert_node.arrow());
        let comp = ProgNode::comp(node, assert_node).unwrap();
        println!("l6: {}", comp.arrow());
        // let node2 = ProgNode::assert(&node, Cmr::unit()).unwrap();
        // println!("l3: {}", node2.arrow());
        // let node3 = ProgNode::comp(&ProgNode::pair(&ProgNode::unit(), &ProgNode::unit()).unwrap(), &node2).unwrap();
        // println!("l4: {}", node3.arrow());
        let res = comp.finalize_types_main().unwrap();
        dbg!(&res);
    }
}
