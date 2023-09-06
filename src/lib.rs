/// Library for parsing and compiling simp-lang

pub type ProgNode = Arc<named::NamedConstructNode>;

pub mod compile;
pub mod dummy_env;
pub mod named;
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
    named::{NamedCommitNode, NamedExt},
    parse::{PestParse, Program},
    scope::GlobalScope,
};

#[derive(Parser)]
#[grammar = "minimal.pest"]
pub struct IdentParser;

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct WitFileData {
    pub map: HashMap<String, String>,
}

pub fn _compile(file: &Path) -> Arc<Node<Named<Commit<Elements>>>> {
    let file = std::fs::read_to_string(file).unwrap();
    let mut pairs = IdentParser::parse(Rule::program, &file).unwrap_or_else(|e| panic!("{}", e));

    let prog = Program::parse(pairs.next().unwrap());

    let mut scope = GlobalScope::new();
    let simplicity_prog = prog.eval(&mut scope);
    let commit_node = simplicity_prog
        .finalize_types_main()
        .expect("Type check error");
    commit_node
}

pub fn compile(file: &Path) -> CommitNode<Elements> {
    let node = _compile(file);
    Arc::try_unwrap(node.to_commit_node()).unwrap()
}

pub fn satisfy(prog: &Path, wit_file: &Path) -> RedeemNode<Elements> {
    let commit_node = _compile(prog);
    let simplicity_prog =
        Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");

    let file = std::fs::File::open(wit_file).expect("Error opening witness file");
    let rdr = std::io::BufReader::new(file);
    let mut wit_data: WitFileData =
        serde_json::from_reader(rdr).expect("Error reading witness file");

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
                    let bytes: Vec<u8> = hex_conservative::FromHex::from_hex(&wit).unwrap();
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
                        assert!(bit_iter.next().unwrap() == false);
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

    let redeem_prog = simplicity_prog
        .convert::<NoSharing, Redeem<Elements>, _>(&mut wit_data)
        .unwrap();
    Arc::try_unwrap(redeem_prog).unwrap()
}

#[cfg(test)]
mod tests {
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use pest::Parser;
    use simplicity::{
        dag::{NoSharing, PostOrderIterItem},
        encode,
        node::{Commit, Converter, Inner, Redeem, RedeemData},
        BitMachine, BitWriter, Cmr, Value,
    };

    use crate::{
        named::{ConstructExt, Named, NamedCommitNode, NamedExt, ProgExt},
        parse::{PestParse, Program, Statement},
        scope::GlobalScope,
        *,
    };

    #[test]
    fn test_progs() {
        _test_progs("./test.txt");
        _test_progs("./assertr.txt");
        _test_progs("./scopes.txt");
        _test_progs("./nesting.txt");
        _test_progs("./add.txt");
        // _test_progs("./add_with_builtins.txt");
    }

    fn _test_progs(file: &str) {
        let file = std::fs::read_to_string(file).unwrap();
        let pairs = IdentParser::parse(Rule::program, &file).unwrap_or_else(|e| panic!("{}", e));

        let mut stmts = Vec::new();
        for pair in pairs {
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
        // let commit_node = commit_node.to_commit_node();
        let simplicity_prog =
            Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");
        dbg!(&simplicity_prog);
        let mut vec = Vec::new();
        let mut writer = BitWriter::new(&mut vec);
        let _encoded = encode::encode_program(&simplicity_prog, &mut writer).unwrap();
        println!("{}", Base64Display::new(&vec, &STANDARD));

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

            // fn convert_witness(
            //     &mut self,
            //     _: &PostOrderIterItem<&CommitNode<Elements>>,
            //     _: &NoWitness,
            // ) -> Result<Arc<Value>, Self::Error> {
            //     Ok(Value::u32(20))
            // }

            // fn convert_disconnect(
            //     &mut self,
            //     _: &PostOrderIterItem<&CommitNode<Elements>>,
            //     _: Option<&Arc<RedeemNode<Elements>>>,
            //     _: &NoDisconnect,
            // ) -> Result<Arc<RedeemNode<Elements>>, Self::Error> {
            //     Err(())
            // }

            // fn convert_data(
            //     &mut self,
            //     data: &PostOrderIterItem<&CommitNode<Elements>>,
            //     inner: Inner<
            //         &Arc<RedeemNode<Elements>>,
            //         Elements,
            //         &Arc<RedeemNode<Elements>>,
            //         &Arc<Value>,
            //     >,
            // ) -> Result<Arc<RedeemData<Elements>>, Self::Error> {
            //     let converted_data = inner
            //         .map(|node| node.cached_data())
            //         .map_disconnect(|node| node.cached_data())
            //         .map_witness(Arc::clone);
            //     Ok(Arc::new(RedeemData::new(
            //         data.node.arrow().shallow_clone(),
            //         converted_data,
            //     )))
            // }
        }

        let redeem_prog = simplicity_prog
            .convert::<NoSharing, Redeem<Elements>, _>(&mut MyConverter)
            .unwrap();
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
        let node = ProgNode::comp(inp, node);
        println!("l2: {}", node.arrow());
        let node = ProgNode::pair(node, ProgNode::unit());
        println!("l3: {}", node.arrow());
        let later_operation = ProgNode::take(ProgNode::unit());
        println!("l4: {}", later_operation.arrow());
        let assert_node = ProgNode::assertl(later_operation, Cmr::unit());
        println!("l5: {}", assert_node.arrow());
        let comp = ProgNode::comp(node, assert_node);
        println!("l6: {}", comp.arrow());
        // let node2 = ProgNode::assert(&node, Cmr::unit()).unwrap();
        // println!("l3: {}", node2.arrow());
        // let node3 = ProgNode::comp(&ProgNode::pair(&ProgNode::unit(), &ProgNode::unit()).unwrap(), &node2).unwrap();
        // println!("l4: {}", node3.arrow());
        let res = comp.finalize_types_main().unwrap();
        dbg!(&res);
    }
}
