use std::collections::HashMap;

use elements::secp256k1_zkp as secp256k1;
use secp256k1::hashes::{sha256, Hash, HashEngine};
use simplicityhl::types::TypeConstructible;
use simplicityhl::value::ValueConstructible;
use simplicityhl::{
    elements, ResolvedType, TemplateProgramWitness, UnstableFeatures, Value, WitnessNameToValueMap,
};

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
            .template_path("../examples/p2pk.simf")
            .arguments(p2pk_args())
            .witness(p2pk),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to public key hash")
            .program_path("../examples/p2pkh.simf")
            .witness(p2pkh),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to multisig")
            .program_path("../examples/p2ms.simf")
            .witness(p2ms),
        // Pruned spends: the node rejects programs with unexecuted branches or unread
        // witness data, so these check what pruning produces against the real node.
        TestCase::new(&daemon, genesis_hash)
            .name("OP_CAT (pruned)")
            .program_path("../examples/cat.simf")
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("HODL vault (pruned)")
            .program_path("../examples/hodl_vault.simf")
            .witness(hodl_vault)
            .lock_time(elements::LockTime::from_consensus(1000))
            .sequence(elements::Sequence::ENABLE_LOCKTIME_NO_RBF)
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to public key (pruned)")
            .template_path("../examples/p2pk.simf")
            .arguments(p2pk_args())
            .witness(p2pk)
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to public key hash (pruned)")
            .program_path("../examples/p2pkh.simf")
            .witness(p2pkh)
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Pay to multisig (pruned)")
            .program_path("../examples/p2ms.simf")
            .witness(p2ms)
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Kitchen sink (pruned)")
            .template_path_with_unstable("../examples/kitchen_sink.simf", &UnstableFeatures::all())
            .arguments_file("../examples/kitchen_sink.args")
            .witness_file("../examples/kitchen_sink.wit")
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Witness read only by a hidden branch (pruned)")
            .program_path("../fixtures/pruning_hidden_witness.simf")
            .witness_file("../fixtures/pruning_hidden_witness.none.wit")
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Witness read by the taken branch (pruned)")
            .program_path("../fixtures/pruning_hidden_witness.simf")
            .witness_file("../fixtures/pruning_hidden_witness.eq.wit")
            .pruned(),
        TestCase::new(&daemon, genesis_hash)
            .name("Identical case nodes taking different branches (pruned)")
            .program_path("../fixtures/pruning_twin_cases.simf")
            .pruned(),
    ];
    tests.iter_mut().for_each(TestCase::create_utxo);
    daemon.generate(1000); // satisfies lock time of all test cases
    let mut rejected = vec![];
    for test in tests {
        println!("⏳ {}", test.name);
        match test.spend_utxo() {
            Ok(()) => println!("✅ {}", test.name),
            Err(error) => {
                println!("❌ {}: {error}", test.name);
                rejected.push(test.name);
            }
        }
    }
    assert!(rejected.is_empty(), "rejected spends: {rejected:?}");
}

fn hodl_vault(sighash_all: [u8; 32]) -> simplicityhl::WitnessValues {
    let mut witness_values = HashMap::new();
    let oracle_height = 1000;
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("ORACLE_HEIGHT"),
        Value::u32(oracle_height),
    );
    let oracle_price = 100_000;
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("ORACLE_PRICE"),
        Value::u32(oracle_price),
    );
    let mut hasher = sha256::HashEngine::default();
    hasher.input(&oracle_height.to_be_bytes());
    hasher.input(&oracle_price.to_be_bytes());
    let oracle_hash = sha256::Hash::from_engine(hasher).to_byte_array();
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("ORACLE_SIG"),
        Value::byte_array(util::sign_schnorr(1, oracle_hash)),
    );
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("OWNER_SIG"),
        Value::byte_array(util::sign_schnorr(2, sighash_all)),
    );
    simplicityhl::WitnessValues::from_map(witness_values)
}

fn p2pk_args() -> simplicityhl::Arguments {
    simplicityhl::Arguments::from_map(HashMap::from([(
        TemplateProgramWitness::parameter_from_str("ALICE_PUBLIC_KEY"),
        Value::u256(util::xonly_public_key(1)),
    )]))
}

fn p2pk(sighash_all: [u8; 32]) -> simplicityhl::WitnessValues {
    simplicityhl::WitnessValues::from_map(HashMap::from([(
        TemplateProgramWitness::witness_from_str("ALICE_SIGNATURE"),
        Value::byte_array(util::sign_schnorr(1, sighash_all)),
    )]))
}

fn p2pkh(sighash_all: [u8; 32]) -> simplicityhl::WitnessValues {
    let mut witness_values = HashMap::new();
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("PK"),
        Value::u256(util::xonly_public_key(1)),
    );
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("SIG"),
        Value::byte_array(util::sign_schnorr(1, sighash_all)),
    );
    simplicityhl::WitnessValues::from_map(witness_values)
}

fn p2ms(sighash_all: [u8; 32]) -> simplicityhl::WitnessValues {
    let mut witness_values = HashMap::new();
    let sig1 = Value::some(Value::byte_array(util::sign_schnorr(1, sighash_all)));
    let sig2 = Value::none(ResolvedType::byte_array(64));
    let sig3 = Value::some(Value::byte_array(util::sign_schnorr(3, sighash_all)));
    let ty = sig1.ty().clone();
    let maybe_sigs = Value::array([sig1, sig2, sig3], ty);
    witness_values.insert(
        TemplateProgramWitness::witness_from_str("MAYBE_SIGS"),
        maybe_sigs,
    );
    simplicityhl::WitnessValues::from_map(witness_values)
}
