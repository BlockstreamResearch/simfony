use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::Arc;

use elements::pset::PartiallySignedTransaction as Psbt;
use elements::{confidential, secp256k1_zkp as secp256k1};
use elementsd::bitcoincore_rpc::jsonrpc::serde_json;
use elementsd::ElementsD;
use secp256k1::XOnlyPublicKey;
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicityhl::ast::ElementsJetHinter;
use simplicityhl::{elements, simplicity, UnresolvedValues, UnstableFeatures};

use crate::common::daemon::Call;

type FnWitness = fn([u8; 32]) -> simplicityhl::WitnessValues;

pub struct TestCase<'a> {
    pub name: &'static str,
    template: Option<simplicityhl::TemplateAst>,
    compiled: Option<simplicityhl::CompiledProgram>,
    witness: FnWitness,
    witness_file: Option<PathBuf>,
    pruned: bool,
    lock_time: elements::LockTime,
    sequence: elements::Sequence,
    daemon: &'a ElementsD,
    genesis_hash: elements::BlockHash,
    funding: Option<Funding>,
}

#[derive(Clone)]
struct Funding {
    address: elements::Address,
    txid: elements::Txid,
}

impl<'a> TestCase<'a> {
    pub fn new(daemon: &'a ElementsD, genesis_hash: elements::BlockHash) -> Self {
        Self {
            name: "test name is missing",
            template: None,
            compiled: None,
            witness: empty_witness,
            witness_file: None,
            pruned: false,
            lock_time: elements::LockTime::ZERO,
            sequence: elements::Sequence::ZERO,
            daemon,
            genesis_hash,
            funding: None,
        }
    }

    pub fn name(mut self, name: &'static str) -> Self {
        self.name = name;
        self
    }

    pub fn program_path<P: AsRef<Path>>(mut self, path: P) -> Self {
        let text = read_file(path);
        let compiled = simplicityhl::CompiledProgram::new(
            text.as_str(),
            simplicityhl::Arguments::default(),
            false,
            Box::new(ElementsJetHinter::new()),
        )
        .expect("program should compile");
        self.compiled = Some(compiled);
        self
    }

    pub fn template_path<P: AsRef<Path>>(self, path: P) -> Self {
        self.template_path_with_unstable(path, &UnstableFeatures::none())
    }

    pub fn template_path_with_unstable<P: AsRef<Path>>(
        mut self,
        path: P,
        unstable_features: &UnstableFeatures,
    ) -> Self {
        let text = read_file(path);
        let template = simplicityhl::TemplateAst::new_with_unstable(
            text.as_str(),
            unstable_features,
            Box::new(ElementsJetHinter::new()),
        )
        .expect("program should compile");
        self.template = Some(template);
        self
    }

    pub fn arguments_file<P: AsRef<Path>>(self, path: P) -> Self {
        let parameters = self
            .template
            .as_ref()
            .expect("template should exist")
            .parameters();
        let arguments = read_values(path)
            .resolve(parameters)
            .expect("arguments should be consistent with the program");
        self.arguments(arguments)
    }

    pub fn arguments(mut self, arguments: simplicityhl::Arguments) -> Self {
        let compiled = self
            .template
            .as_ref()
            .expect("template should exist")
            .instantiate(arguments, false)
            .expect("arguments should be consistent with the program");
        self.compiled = Some(compiled);
        self
    }

    pub fn witness(mut self, witness: FnWitness) -> Self {
        self.witness = witness;
        self
    }

    /// Read the witness from a file. Use this for witnesses that do not sign the transaction.
    pub fn witness_file<P: AsRef<Path>>(mut self, path: P) -> Self {
        self.witness_file = Some(path.as_ref().to_path_buf());
        self
    }

    /// Prune the program against the spending transaction before it is broadcast.
    pub fn pruned(mut self) -> Self {
        self.pruned = true;
        self
    }

    pub fn lock_time(mut self, lock_time: elements::LockTime) -> Self {
        self.lock_time = lock_time;
        self
    }

    pub fn sequence(mut self, sequence: elements::Sequence) -> Self {
        self.sequence = sequence;
        self
    }

    fn script_ver(&self) -> (elements::Script, elements::taproot::LeafVersion) {
        let script = elements::script::Script::from(
            self.compiled
                .as_ref()
                .expect("program should be defined")
                .commit()
                .cmr()
                .as_ref()
                .to_vec(),
        );
        (script, simplicity::leaf_version())
    }

    fn taproot_spend_info(&self) -> elements::taproot::TaprootSpendInfo {
        let internal_key = XOnlyPublicKey::from_str(
            "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0",
        )
        .unwrap();
        let builder = elements::taproot::TaprootBuilder::new();
        let (script, version) = self.script_ver();
        let builder = builder
            .add_leaf_with_ver(0, script, version)
            .expect("tap tree should be valid");
        builder
            .finalize(secp256k1::SECP256K1, internal_key)
            .expect("tap tree should be valid")
    }

    // Find the Outpoint by value.
    // Ideally, we should find by scriptPubkey, but this
    // works for temp test case
    fn get_vout(&self) -> (elements::OutPoint, elements::TxOut) {
        let funding = self.funding.as_ref().expect("test funding is missing");
        let tx = self.daemon.get_transaction(&funding.txid);
        let script = funding.address.script_pubkey();
        for (vout, txout) in tx.output.into_iter().enumerate() {
            if txout.value == confidential::Value::Explicit(100_000_000)
                && txout.script_pubkey == script
            {
                return (elements::OutPoint::new(funding.txid, vout as u32), txout);
            }
        }
        unreachable!("Only call get vout on functions which have the expected outpoint");
    }

    pub fn create_utxo(&mut self) {
        let info = self.taproot_spend_info();
        let blinder = None;
        let address = elements::Address::p2tr(
            secp256k1::SECP256K1,
            info.internal_key(),
            info.merkle_root(),
            blinder,
            &elements::AddressParams::ELEMENTS,
        );
        let amount = "1";
        let txid = self.daemon.send_to_address(&address, amount);
        self.funding = Some(Funding { address, txid });
    }

    /// Spend the funding output, returning the reason if the program cannot be satisfied
    /// or the node rejects the spend.
    pub fn spend_utxo(&self) -> Result<(), String> {
        let compiled = self.compiled.as_ref().expect("test program is missing");
        let (outpoint, utxo) = self.get_vout();
        let mut psbt = Psbt::from_tx(elements::Transaction {
            version: 2,
            lock_time: self.lock_time,
            input: vec![elements::TxIn {
                previous_output: outpoint,
                is_pegin: false,
                script_sig: elements::Script::new(),
                sequence: self.sequence,
                asset_issuance: elements::AssetIssuance::null(),
                witness: elements::TxInWitness::empty(),
            }],
            output: vec![
                elements::TxOut {
                    value: confidential::Value::Explicit(99_997_000),
                    script_pubkey: self.daemon.get_new_address().script_pubkey(),
                    asset: utxo.asset,
                    nonce: confidential::Nonce::Null,
                    witness: elements::TxOutWitness::empty(),
                },
                elements::TxOut::new_fee(3_000, utxo.asset.explicit().unwrap()),
            ],
        });
        let info = self.taproot_spend_info();
        let script_ver = self.script_ver();
        let control_block = info
            .control_block(&script_ver)
            .expect("control block should exist");
        let env = {
            let tx = psbt
                .extract_tx()
                .expect("transaction should be extractable");
            let utxos = vec![ElementsUtxo::from(utxo)];
            let index = 0;
            let annex = None;
            ElementsEnv::new(
                Arc::new(tx),
                utxos,
                index,
                compiled.commit().cmr(),
                control_block.clone(),
                annex,
                self.genesis_hash,
            )
        };
        let witness_values = match &self.witness_file {
            Some(path) => read_values(path)
                .resolve(compiled.witness_types())
                .expect("witness should be consistent with the program"),
            None => (self.witness)(env.c_tx_env().sighash_all().to_byte_array()),
        };
        let satisfied_program = compiled
            .satisfy_with_env(witness_values, self.pruned.then_some(&env))
            .map_err(|error| format!("program is not satisfiable: {error}"))?;
        let (program_bytes, witness_bytes) = satisfied_program.redeem().to_vec_with_witness();
        psbt.inputs_mut()[0].final_script_witness = Some(elements::Witness::from(vec![
            witness_bytes,
            program_bytes,
            script_ver.0.into_bytes(),
            control_block.serialize(),
        ]));
        let tx = psbt
            .extract_tx()
            .expect("transaction should be extractable");

        self.daemon.send_raw_transaction(&tx).map(|_txid| ())
    }
}

fn empty_witness(_sighash_all: [u8; 32]) -> simplicityhl::WitnessValues {
    simplicityhl::WitnessValues::default()
}

fn read_file<P: AsRef<Path>>(path: P) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(path))
        .expect("path should be readable")
}

fn read_values<P: AsRef<Path>>(path: P) -> UnresolvedValues {
    serde_json::from_str(&read_file(path)).expect("values file should be valid JSON")
}
