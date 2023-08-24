/// Library for parsing and compiling simp-lang

pub type ProgNode = Arc<ConstructNode<Elements>>;

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
            Commit, Converter, CoreConstructible, Inner, JetConstructible, NoDisconnect, NoWitness,
            Redeem, RedeemData, SimpleFinalizer,
        },
        BitMachine, BitWriter, Cmr, CommitNode, RedeemNode, Value,
    };

    use crate::{
        parse::{PestParse, Program, Statement},
        scope::GlobalScope,
        *,
    };

    #[test]
    fn test_progs() {
        _test_progs("./test.txt");
        _test_progs("./assertr.txt");
        // _test_progs("./scopes.txt");
        // _test_progs("./nesting.txt");
        // _test_progs("./add.txt");
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
        simplicity_prog.encode(&mut writer).unwrap();
        println!("{}", Base64Display::new(&vec, &STANDARD));
        dbg!(&simplicity_prog);
        let commit_node = simplicity_prog.finalize_types().expect("Type check error");
        let simplicity_prog =
            Arc::<_>::try_unwrap(commit_node).expect("Only one reference to commit node");
        dbg!(&simplicity_prog);
        let encoded = simplicity_prog.encode_to_vec();
        println!("{}", Base64Display::new(&encoded, &STANDARD));
        let v: Vec<Arc<Value>> = vec![];
        let mut finalizer = SimpleFinalizer::new(v.into_iter());

        struct MyConverter;

        impl Converter<Commit<Elements>, Redeem<Elements>> for MyConverter {
            type Error = ();

            fn convert_witness(
                &mut self,
                _: &PostOrderIterItem<&CommitNode<Elements>>,
                _: &NoWitness,
            ) -> Result<Arc<Value>, Self::Error> {
                Ok(Value::u32(10))
            }

            fn convert_disconnect(
                &mut self,
                _: &PostOrderIterItem<&CommitNode<Elements>>,
                _: Option<&Arc<RedeemNode<Elements>>>,
                _: &NoDisconnect,
            ) -> Result<Arc<RedeemNode<Elements>>, Self::Error> {
                Err(())
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&CommitNode<Elements>>,
                inner: Inner<
                    &Arc<RedeemNode<Elements>>,
                    Elements,
                    &Arc<RedeemNode<Elements>>,
                    &Arc<Value>,
                >,
            ) -> Result<Arc<RedeemData<Elements>>, Self::Error> {
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

        let redeem_prog = simplicity_prog.finalize(&mut finalizer).unwrap();
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
        let node = ProgNode::comp(&inp, &node).unwrap();
        println!("l2: {}", node.arrow());
        let node = ProgNode::pair(&node, &ProgNode::unit()).unwrap();
        println!("l3: {}", node.arrow());
        let later_operation = ProgNode::take(&ProgNode::unit());
        println!("l4: {}", later_operation.arrow());
        let assert_node = ProgNode::assertl(&later_operation, Cmr::unit()).unwrap();
        println!("l5: {}", assert_node.arrow());
        let comp = ProgNode::comp(&node, &assert_node).unwrap();
        println!("l6: {}", comp.arrow());
        // let node2 = ProgNode::assert(&node, Cmr::unit()).unwrap();
        // println!("l3: {}", node2.arrow());
        // let node3 = ProgNode::comp(&ProgNode::pair(&ProgNode::unit(), &ProgNode::unit()).unwrap(), &node2).unwrap();
        // println!("l4: {}", node3.arrow());
        let res = comp.finalize_types().unwrap();
        dbg!(&res);
    }
}
