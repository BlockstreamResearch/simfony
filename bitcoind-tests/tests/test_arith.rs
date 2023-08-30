//! # rust-miniscript integration test
//!
//! Arith expression fragment integration tests
//!

use std::fs::File;
use std::path::Path;
use std::str::FromStr;

use elementsd::bitcoincore_rpc::bitcoin::ScriptBuf;
use ::secp256k1::XOnlyPublicKey;
use simp_lang::elements::BlockHash;
use simp_lang::elements::address::Payload;
use simp_lang::elements::taproot::TaprootBuilder;
use simp_lang::simplicity::{RedeemNode, BitIter};
use simp_lang::simplicity::jet::Elements;
use simp_lang::simplicity::node::SimpleFinalizer;
use simp_lang::{elements, simplicity};

use elements::pset::PartiallySignedTransaction as Psbt;
use elements::sighash::SigHashCache;
use elements::taproot::{LeafVersion, TapLeafHash};
use elements::{
    confidential, pset as psbt, secp256k1_zkp as secp256k1, sighash, OutPoint, Script, Sequence,
    TxIn, TxOut, Txid,
};
use elementsd::ElementsD;
use rand::RngCore;
mod setup;
use setup::test_util::{self, TestData, PARAMS};
use setup::Call;
use actual_rand as rand;

type CommitProg = simplicity::CommitNode<Elements>;
type RedeemProg = simplicity::RedeemNode<Elements>;

// Find the Outpoint by value.
// Ideally, we should find by scriptPubkey, but this
// works for temp test case
fn get_vout(cl: &ElementsD, txid: Txid, value: u64, spk: Script) -> (OutPoint, TxOut) {
    let tx = cl.get_transaction(&txid);
    for (i, txout) in tx.output.into_iter().enumerate() {
        if txout.value == confidential::Value::Explicit(value) && txout.script_pubkey == spk {
            return (OutPoint::new(txid, i as u32), txout);
        }
    }
    unreachable!("Only call get vout on functions which have the expected outpoint");
}

pub fn test_simplicity(cl: &ElementsD, prog: &str, witness_file: &str) {
    let prog = Path::new(prog);
    let witness_file = Path::new(witness_file);
    let secp = secp256k1::Secp256k1::new();
    let internal_key = XOnlyPublicKey::from_str("f5919fa64ce45f8306849072b26c1bfdd2937e6b81774796ff372bd1eb5362d2").unwrap();

    let commit_prog = simp_lang::compile(&prog);
    let builder = TaprootBuilder::new();
    let script = elements::script::Script::from(commit_prog.cmr().as_ref().to_vec());
    let script_ver = (script, LeafVersion::from_u8(0xbe).unwrap());
    let builder = builder.add_leaf_with_ver(0, script_ver.0.clone(), script_ver.1).unwrap();
    let data = builder.finalize(&secp, internal_key).unwrap();
    let addr = elements::Address::p2tr(&secp, internal_key, data.merkle_root(), None, &PARAMS);
    let txid = cl.send_to_address(&addr, "1");
    cl.generate(1);
    println!("txid: {}", txid);
    let (outpoint, witness_utxo) = get_vout(cl, txid, 100_000_000, addr.script_pubkey());
    println!("outpoint: {:?}", outpoint);
    let mut psbt = Psbt::new_v2();
    let txin = TxIn {
        previous_output: outpoint,
        is_pegin: false,
        script_sig: Script::new(),
        sequence: Sequence::from_consensus(1),
        asset_issuance: Default::default(),
        witness: Default::default(),
    };
    psbt.add_input(psbt::Input::from_txin(txin));
    let out = TxOut {
        value: confidential::Value::Explicit(99_997_000),
        script_pubkey: cl.get_new_address().script_pubkey(),
        asset: witness_utxo.asset,
        nonce: confidential::Nonce::Null,
        witness: Default::default(),
    };
    psbt.add_output(psbt::Output::from_txout(out));
    let fee_out = TxOut::new_fee(3_000, witness_utxo.asset.explicit().unwrap());
    psbt.add_output(psbt::Output::from_txout(fee_out));
    let redeem_prog = simp_lang::satisfy(prog, witness_file);
    psbt.inputs_mut()[0].final_script_witness =
    Some(vec![
        redeem_prog.encode_to_vec(),
        script_ver.0.clone().into_bytes(),
        data.control_block(&script_ver).unwrap().serialize(),
    ]);
    let tx = psbt
        .extract_tx()
        .expect("Extraction error");
    let txid = cl.send_raw_transaction(&tx);
    /* Convert desc into elements one by adding a prefix*/
    // let desc = format!("el{}", desc);
    // //
    // let secp = secp256k1::Secp256k1::new();
    // let xonly_keypairs = &testdata.secretdata.x_only_keypairs;
    // let x_only_pks = &testdata.pubdata.x_only_pks;
    // // Generate some blocks
    // cl.generate(1);

    // let definite_desc = test_util::parse_test_desc(&desc, &testdata.pubdata)
    //     .unwrap()
    //     .at_derivation_index(0)
    //     .unwrap();

    // let derived_desc = definite_desc.derived_descriptor(&secp).unwrap();
    // let desc_address = derived_desc.address(&PARAMS).unwrap(); // No blinding

    // // Next send some btc to each address corresponding to the miniscript
    // let txid = cl.send_to_address(&desc_address, "1"); // 1 BTC
    //                                                    // Wait for the funds to mature.
    // cl.generate(2);
    // // Create a PSBT for each transaction.
    // // Spend one input and spend one output for simplicity.
    // let mut psbt = Psbt::new_v2();
    // // figure out the outpoint from the txid
    // let txin = TxIn {
    //     previous_output: outpoint,
    //     is_pegin: false,
    //     script_sig: Script::new(),
    //     sequence: Sequence::from_consensus(1),
    //     asset_issuance: Default::default(),
    //     witness: Default::default(),
    // };
    // psbt.add_input(psbt::Input::from_txin(txin));
    // // Get a new script pubkey from the node so that
    // // the node wallet tracks the receiving transaction
    // // and we can check it by gettransaction RPC.
    // let addr = cl.get_new_address();
    // let out = TxOut {
    //     // Had to decrease 'value', so that fees can be increased
    //     // (Was getting insufficient fees error, for deep script trees)
    //     value: confidential::Value::Explicit(99_997_000),
    //     script_pubkey: addr.script_pubkey(),
    //     asset: witness_utxo.asset,
    //     nonce: confidential::Nonce::Null,
    //     witness: Default::default(),
    // };
    // psbt.add_output(psbt::Output::from_txout(out));
    // // ELEMENTS: Add fee output
    // let fee_out = TxOut::new_fee(3_000, witness_utxo.asset.explicit().unwrap());
    // psbt.add_output(psbt::Output::from_txout(fee_out));

    // psbt.inputs_mut()[0]
    //     .update_with_descriptor_unchecked(&definite_desc)
    //     .unwrap();
    // psbt.inputs_mut()[0].witness_utxo = Some(witness_utxo.clone());

    // // --------------------------------------------
    // // Sign the transactions with all keys
    // // AKA the signer role of psbt
    // // Get all the pubkeys and the corresponding secret keys

    // let unsigned_tx = &psbt.extract_tx().unwrap();
    // let mut sighash_cache = SigHashCache::new(unsigned_tx);
    // match derived_desc {
    //     Descriptor::TrExt(ref tr) => {
    //         let hash_ty = sighash::SchnorrSigHashType::Default;

    //         let prevouts = [witness_utxo];
    //         let prevouts = sighash::Prevouts::All(&prevouts);
    //         // ------------------ script spend -------------
    //         let x_only_keypairs_reqd: Vec<(secp256k1::KeyPair, TapLeafHash)> = tr
    //             .iter_scripts()
    //             .flat_map(|(_depth, ms)| {
    //                 let leaf_hash = TapLeafHash::from_script(&ms.encode(), LeafVersion::default());
    //                 ms.iter_pk().filter_map(move |pk| {
    //                     let i = x_only_pks.iter().position(|&x| x.to_public_key() == pk);
    //                     i.map(|idx| (xonly_keypairs[idx], leaf_hash))
    //                 })
    //             })
    //             .collect();
    //         for (keypair, leaf_hash) in x_only_keypairs_reqd {
    //             let sighash_msg = sighash_cache
    //                 .taproot_script_spend_signature_hash(
    //                     0,
    //                     &prevouts,
    //                     leaf_hash,
    //                     hash_ty,
    //                     testdata.pubdata.genesis_hash,
    //                 )
    //                 .unwrap();
    //             let msg = secp256k1::Message::from_slice(&sighash_msg[..]).unwrap();
    //             let mut aux_rand = [0u8; 32];
    //             rand::thread_rng().fill_bytes(&mut aux_rand);
    //             let sig = secp.sign_schnorr_with_aux_rand(&msg, &keypair, &aux_rand);
    //             // FIXME: uncomment when == is supported for secp256k1::KeyPair. (next major release)
    //             // let x_only_pk = pks[xonly_keypairs.iter().position(|&x| x == keypair).unwrap()];
    //             // Just recalc public key
    //             let x_only_pk = secp256k1::XOnlyPublicKey::from_keypair(&keypair).0;
    //             psbt.inputs_mut()[0].tap_script_sigs.insert(
    //                 (x_only_pk, leaf_hash),
    //                 elements::SchnorrSig { sig, hash_ty },
    //             );
    //         }
    //     }
    //     _ => {
    //         // Non-tr descriptors
    //         panic!("Only testing Tr covenant descriptor")
    //     }
    // }
    // // Add the hash preimages to the psbt
    // psbt.inputs_mut()[0].sha256_preimages.insert(
    //     testdata.pubdata.sha256,
    //     testdata.secretdata.sha256_pre.to_vec(),
    // );
    // println!("Testing descriptor: {}", desc);
    // // Finalize the transaction using psbt
    // // Let miniscript do it's magic!
    // if let Err(e) = psbt.finalize_mall_mut(&secp, testdata.pubdata.genesis_hash) {
    //     // All miniscripts should satisfy
    //     panic!(
    //         "Could not satisfy non-malleably: error{} desc:{} ",
    //         e[0], desc
    //     );
    // }
    // let tx = psbt
    //     .extract(&secp, testdata.pubdata.genesis_hash)
    //     .expect("Extraction error");

    // // Send the transactions to bitcoin node for mining.
    // // Regtest mode has standardness checks
    // // Check whether the node accepts the transactions
    // let txid = cl.send_raw_transaction(&tx);

    // // Finally mine the blocks and await confirmations
    // cl.generate(1);
    // // Get the required transactions from the node mined in the blocks.
    // // Check whether the transaction is mined in blocks
    // // Assert that the confirmations are > 0.
    // let num_conf = cl.call("gettransaction", &[txid.to_string().into()])["confirmations"]
    //     .as_u64()
    //     .unwrap();
    // assert!(num_conf > 0);
    // tx.input[0].witness.script_witness.clone()
}

#[test]
fn test_arith() {
    let (cl, _, _genesis_hash) = &setup::setup(false);
    // let testdata = TestData::new_fixed_data(50, *genesis_hash);
    println!("{}", cl.get_new_address());

    test_simplicity(cl, "../add.txt", "../empty.witness");
    test_simplicity(cl, "../scopes.txt", "../empty.witness");
    // test_simplicity(cl, "../add_with_builtins.txt", "../empty.witness");
    // test_simplicity(cl, "../assertr.txt", "../empty.witness");
    test_simplicity(cl, "../nesting.txt", "../empty.witness");
    test_simplicity(cl, "../test.txt", "../test.witness");
    // test_descs(cl, &testdata);
}
