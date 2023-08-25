/// Library for parsing and compiling simp-lang

pub type ProgNode = Arc<named::NamedConstructNode>;

pub mod compile;
pub mod dummy_env;
pub mod named;
pub mod parse;
pub mod scope;

use std::sync::Arc;

use pest_derive::Parser;
use simplicity::{jet::Elements, ConstructNode};

#[derive(Parser)]
#[grammar = "minimal.pest"]
pub struct IdentParser;

#[cfg(test)]
mod tests {
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use pest::Parser;
    use simplicity::{
        dag::PostOrderIterItem,
        node::{
            Commit, Converter, Inner, NoDisconnect, NoWitness,
            Redeem, RedeemData, SimpleFinalizer,
        },
        BitMachine, BitWriter, Cmr, CommitNode, RedeemNode, Value, encode,
    };

    use crate::{
        parse::{PestParse, Program, Statement},
        scope::GlobalScope,
        *, named::{ConstructExt, NamedExt, ProgExt, Named},
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
        let commit_node = simplicity_prog.finalize_types_main().expect("Type check error");
        // let commit_node = commit_node.to_commit_node();
        let simplicity_prog =
            Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");
        dbg!(&simplicity_prog);
        let mut vec = Vec::new();
        let mut writer = BitWriter::new(&mut vec);
        let _encoded = encode::encode_program(&simplicity_prog, &mut writer).unwrap();
        println!("{}", Base64Display::new(&vec, &STANDARD));
        let v: Vec<Arc<Value>> = vec![];

        struct MyConverter;

        impl Converter<Named<Commit<Elements>>, Redeem<Elements>> for MyConverter {
            type Error = ();

            fn convert_witness(
                &mut self,
                data: &PostOrderIterItem<&simplicity::node::Node<Named<Commit<Elements>>>>,
                witness: &<Named<Commit<Elements>> as simplicity::node::Marker>::Witness,
            ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Witness, Self::Error> {
                todo!()
            }

            fn convert_disconnect(
                &mut self,
                data: &PostOrderIterItem<&simplicity::node::Node<Named<Commit<Elements>>>>,
                maybe_converted: Option<&Arc<simplicity::node::Node<Redeem<Elements>>>>,
                disconnect: &<Named<Commit<Elements>> as simplicity::node::Marker>::Disconnect,
            ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Disconnect, Self::Error> {
                todo!()
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&simplicity::node::Node<Named<Commit<Elements>>>>,
                inner: Inner<&Arc<simplicity::node::Node<Redeem<Elements>>>, <Redeem<Elements> as simplicity::node::Marker>::Jet, &<Redeem<Elements> as simplicity::node::Marker>::Disconnect, &<Redeem<Elements> as simplicity::node::Marker>::Witness>,
            ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::CachedData, Self::Error> {
                todo!()
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

        let redeem_prog = simplicity_prog.finalize(&mut MyConverter).unwrap();
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
