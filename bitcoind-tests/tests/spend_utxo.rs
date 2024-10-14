use elements::hashes::Hash;
use elements::secp256k1_zkp as secp256k1;
use secp256k1::hashes::{sha256, HashEngine};
use simfony::str::WitnessName;
use simfony::types::TypeConstructible;
use simfony::value::ValueConstructible;
use simfony::{elements, ResolvedType, Value};

mod common;
use common::daemon::{self, Call};
use common::test::TestCase;
use common::util;

#[test]
fn spend_utxo() {
    let (daemon, genesis_hash) = daemon::setup();
    let mut tests = [
        TestCase::new(&daemon, genesis_hash)
            .name("OP_CAT")
            .program_path("../examples/cat.simf"),
        TestCase::new(&daemon, genesis_hash)
            .name("HODL vault")
            .program_path("../examples/hodl_vault.simf")
            .witness(hodl_vault)
            .lock_time(elements::LockTime::from_consensus(1000))
            .sequence(elements::Sequence::ENABLE_LOCKTIME_NO_RBF),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to public key")
            .program_path("../examples/p2pk.simf")
            .witness(p2pk),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to public key hash")
            .program_path("../examples/p2pkh.simf")
            .witness(p2pkh),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to multisig")
            .program_path("../examples/p2ms.simf")
            .witness(p2ms),
    ];
    tests.iter_mut().for_each(TestCase::create_utxo);
    daemon.generate(1000); // satisfies lock time of all test cases
    for test in tests {
        println!("⏳ {}", test.name);
        test.spend_utxo();
        println!("✅ {}", test.name);
    }
}

fn hodl_vault(sighash_all: [u8; 32]) -> simfony::WitnessValues {
    let mut witness_values = simfony::WitnessValues::default();
    let oracle_height = 1000;
    witness_values
        .insert(
            WitnessName::from_str_unchecked("ORACLE_HEIGHT"),
            Value::u32(oracle_height),
        )
        .unwrap();
    let oracle_price = 100_000;
    witness_values
        .insert(
            WitnessName::from_str_unchecked("ORACLE_PRICE"),
            Value::u32(oracle_price),
        )
        .unwrap();
    let mut hasher = sha256::HashEngine::default();
    hasher.input(&oracle_height.to_be_bytes());
    hasher.input(&oracle_price.to_be_bytes());
    let oracle_hash = sha256::Hash::from_engine(hasher).to_byte_array();
    witness_values
        .insert(
            WitnessName::from_str_unchecked("ORACLE_SIG"),
            Value::byte_array(util::sign_schnorr(1, oracle_hash)),
        )
        .unwrap();
    witness_values
        .insert(
            WitnessName::from_str_unchecked("OWNER_SIG"),
            Value::byte_array(util::sign_schnorr(2, sighash_all)),
        )
        .unwrap();
    witness_values
}

fn p2pk(sighash_all: [u8; 32]) -> simfony::WitnessValues {
    let mut witness_values = simfony::WitnessValues::default();
    witness_values
        .insert(
            WitnessName::from_str_unchecked("SIG"),
            Value::byte_array(util::sign_schnorr(1, sighash_all)),
        )
        .unwrap();
    witness_values
}

fn p2pkh(sighash_all: [u8; 32]) -> simfony::WitnessValues {
    let mut witness_values = simfony::WitnessValues::default();
    witness_values
        .insert(
            WitnessName::from_str_unchecked("PK"),
            Value::u256(util::xonly_public_key(1)),
        )
        .unwrap();
    witness_values
        .insert(
            WitnessName::from_str_unchecked("SIG"),
            Value::byte_array(util::sign_schnorr(1, sighash_all)),
        )
        .unwrap();
    witness_values
}

fn p2ms(sighash_all: [u8; 32]) -> simfony::WitnessValues {
    let mut witness_values = simfony::WitnessValues::default();
    let sig1 = Value::some(Value::byte_array(util::sign_schnorr(1, sighash_all)));
    let sig2 = Value::none(ResolvedType::byte_array(64));
    let sig3 = Value::some(Value::byte_array(util::sign_schnorr(3, sighash_all)));
    let ty = sig1.ty().clone();
    let maybe_sigs = Value::array([sig1, sig2, sig3], ty);
    witness_values
        .insert(WitnessName::from_str_unchecked("MAYBE_SIGS"), maybe_sigs)
        .unwrap();
    witness_values
}
