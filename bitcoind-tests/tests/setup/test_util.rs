//! # Miniscript integration test file format
//!
//! This file has custom parsing for miniscripts that enables satisfier to spend transaction
//!
//! K : Compressed key available
//! K!: Compressed key with corresponding secret key unknown
//! X: X-only key available
//! X!: X-only key with corresponding secret key unknown
//!
//! Example:
//! pk(K1)/pkh(X1)/multi(n,...K3,...) represents a compressed key 'K1'/(X-only key 'X1') whose private key in known by the wallet
//! pk(K2!)/pkh(K3!)/multi(n,...K5!,...) represents a key 'K' whose private key is NOT known to the test wallet
//! sha256(H)/hash256(H)/ripemd160(H)/hash160(H) is hash node whose preimage is known to wallet
//! sha256(H!)/hash256(H!)/ripemd160(H!)/hash160(H!) is hash node whose preimage is *NOT* known to wallet
//! timelocks are taken from the transaction value.
//!
//! The keys/hashes are automatically translated so that the tests knows how to satisfy things that don't end with !
//!

use std::collections::HashMap;

use secp256k1::hashes::{sha256, Hash};
use simp_lang::elements::{AddressParams, self, confidential, BlockHash};
use simp_lang::simplicity::elements::bitcoin;


pub static PARAMS: AddressParams = AddressParams::ELEMENTS;

#[derive(Clone, Debug)]
pub struct PubData {
    pub pks: Vec<bitcoin::PublicKey>,
    pub x_only_pks: Vec<bitcoin::key::XOnlyPublicKey>,
    pub sha256: sha256::Hash,
    pub genesis_hash: elements::BlockHash,
    pub values: HashMap<String, confidential::Value>,
    pub assets: HashMap<String, confidential::Asset>,
    pub spks: HashMap<String, elements::Script>,

    // price oracle test data
    pub timestamp: u64,
    pub price: i64,
}

#[derive(Debug, Clone)]
pub struct SecretData {
    pub sks: Vec<bitcoin::secp256k1::SecretKey>,
    pub x_only_keypairs: Vec<bitcoin::key::KeyPair>,
    pub sha256_pre: [u8; 32],
}
#[derive(Debug, Clone)]
pub struct TestData {
    pub pubdata: PubData,
    pub secretdata: SecretData,
}

// Setup (sk, pk) pairs
fn setup_keys(
    n: usize,
) -> (
    Vec<bitcoin::secp256k1::SecretKey>,
    Vec<bitcoin::PublicKey>,
    Vec<bitcoin::key::KeyPair>,
    Vec<bitcoin::key::XOnlyPublicKey>,
) {
    let secp_sign = secp256k1::Secp256k1::signing_only();
    let mut sk = [0; 32];
    let mut sks = vec![];
    let mut pks = vec![];
    for i in 1..n + 1 {
        sk[0] = i as u8;
        sk[1] = (i >> 8) as u8;
        sk[2] = (i >> 16) as u8;

        let sk = secp256k1::SecretKey::from_slice(&sk[..]).expect("secret key");
        let pk = bitcoin::PublicKey {
            inner: secp256k1::PublicKey::from_secret_key(&secp_sign, &sk),
            compressed: true,
        };
        pks.push(pk);
        sks.push(sk);
    }

    let mut x_only_keypairs = vec![];
    let mut x_only_pks = vec![];

    for sk in &sks {
        let keypair = bitcoin::key::KeyPair::from_secret_key(&secp_sign, sk);
        let (xpk, _parity) = bitcoin::key::XOnlyPublicKey::from_keypair(&keypair);
        x_only_keypairs.push(keypair);
        x_only_pks.push(xpk);
    }
    (sks, pks, x_only_keypairs, x_only_pks)
}

impl TestData {
    // generate a fixed data for n keys
    pub(crate) fn new_fixed_data(n: usize, genesis_hash: BlockHash) -> Self {
        let (sks, pks, x_only_keypairs, x_only_pks) = setup_keys(n);
        let sha256_pre = [0x12; 32];
        let sha256 = sha256::Hash::hash(&sha256_pre);

        let pubdata = PubData {
            pks,
            sha256,
            x_only_pks,
            genesis_hash,
            values: HashMap::new(),
            assets: HashMap::new(),
            spks: HashMap::new(),
            timestamp: 414315315u64, // Some dummy time
            price: 50_000i64,        // Some dummy price
        };
        let secretdata = SecretData {
            sks,
            sha256_pre,
            x_only_keypairs,
        };
        Self {
            pubdata,
            secretdata,
        }
    }
}
