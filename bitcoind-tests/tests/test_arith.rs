//! # rust-miniscript integration test
//!
//! Arith expression fragment integration tests
//!

use std::path::Path;
use std::str::FromStr;

use ::secp256k1::XOnlyPublicKey;
use simfony::elements::taproot::{TaprootBuilder, LeafVersion};
use simfony::elements;
use simfony::SatisfiedProgram;

use elements::pset::PartiallySignedTransaction as Psbt;
use elements::{
    confidential, pset as psbt, secp256k1_zkp as secp256k1, OutPoint, Script, Sequence,
    TxIn, TxOut, Txid,
};
use elementsd::bitcoincore_rpc::jsonrpc::serde_json;
use elementsd::ElementsD;
use simfony::witness::WitnessValues;

mod setup;
use setup::Call;

const PARAMS: elements::AddressParams = elements::AddressParams::ELEMENTS;

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

pub fn test_simplicity(cl: &ElementsD, program_file: &str, witness_file: &str) {
    let program_path = Path::new(program_file);
    let witness_path = Path::new(witness_file);
    let program_text = std::fs::read_to_string(program_path).unwrap();
    let witness_text = std::fs::read_to_string(witness_path).unwrap();
    let witness_values = serde_json::from_str::<WitnessValues>(&witness_text).unwrap();
    let program = SatisfiedProgram::new(&program_text, &witness_values).unwrap();

    let secp = secp256k1::Secp256k1::new();
    let internal_key = XOnlyPublicKey::from_str("f5919fa64ce45f8306849072b26c1bfdd2937e6b81774796ff372bd1eb5362d2").unwrap();

    let builder = TaprootBuilder::new();
    let script = elements::script::Script::from(program.redeem().cmr().as_ref().to_vec());
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
    let (program_bytes, witness_bytes) = program.redeem().encode_to_vec();
    psbt.inputs_mut()[0].final_script_witness =
    Some(vec![
        witness_bytes,
        program_bytes,
        script_ver.0.clone().into_bytes(),
        data.control_block(&script_ver).unwrap().serialize(),
    ]);
    let tx = psbt
        .extract_tx()
        .expect("Extraction error");
    let _txid = cl.send_raw_transaction(&tx);
}

#[test]
fn test_arith() {
    let (cl, _genesis_hash) = &setup::setup();
    println!("{}", cl.get_new_address());

    test_simplicity(cl, "../examples/cat.simf", "../examples/empty.wit");
    // TODO: Other examples require custom signatures
}
