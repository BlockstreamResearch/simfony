//! Dummy Elements environment for testing

use std::sync::Arc;

use elements::{confidential, taproot::ControlBlock, AssetIssuance};
use hashes::Hash;
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicity::Cmr;
use simplicity::{elements, hashes};

/// Return a dummy Elements environment.
pub fn dummy() -> ElementsEnv<Arc<elements::Transaction>> {
    dummy_with(elements::LockTime::ZERO, elements::Sequence::MAX)
}

/// Return a dummy Elements environment with the given locktime and input sequence.
pub fn dummy_with(
    lock_time: elements::LockTime,
    sequence: elements::Sequence,
) -> ElementsEnv<Arc<elements::Transaction>> {
    let ctrl_blk: [u8; 33] = [
        0xc0, 0xeb, 0x04, 0xb6, 0x8e, 0x9a, 0x26, 0xd1, 0x16, 0x04, 0x6c, 0x76, 0xe8, 0xff, 0x47,
        0x33, 0x2f, 0xb7, 0x1d, 0xda, 0x90, 0xff, 0x4b, 0xef, 0x53, 0x70, 0xf2, 0x52, 0x26, 0xd3,
        0xbc, 0x09, 0xfc,
    ];

    ElementsEnv::new(
        Arc::new(elements::Transaction {
            version: 2,
            lock_time,
            // Enable locktime in dummy txin
            input: vec![elements::TxIn {
                previous_output: elements::OutPoint::default(),
                is_pegin: false,
                script_sig: elements::Script::new(),
                sequence,
                asset_issuance: AssetIssuance::default(),
                witness: elements::TxInWitness::default(),
            }],
            output: vec![elements::TxOut {
                asset: confidential::Asset::default(),
                value: confidential::Value::default(),
                nonce: confidential::Nonce::default(),
                script_pubkey: elements::Script::default(),
                witness: elements::TxOutWitness::default(),
            }],
        }),
        vec![ElementsUtxo {
            script_pubkey: elements::Script::default(),
            asset: confidential::Asset::default(),
            value: confidential::Value::default(),
        }],
        0,
        Cmr::from_byte_array([0; 32]),
        ControlBlock::from_slice(&ctrl_blk).unwrap(),
        None,
        elements::BlockHash::all_zeros(),
    )
}
