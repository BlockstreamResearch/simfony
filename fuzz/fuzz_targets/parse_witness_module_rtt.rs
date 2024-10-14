#![no_main]

use libfuzzer_sys::fuzz_target;

use simfony::parse::ParseFromStr;
use simfony::WitnessValues;

fuzz_target!(|witness_values: WitnessValues| {
    let witness_text = witness_values.to_string();
    let parsed_witness_text =
        WitnessValues::parse_from_str(&witness_text).expect("Witness module should be parseable");
    assert_eq!(
        witness_values, parsed_witness_text,
        "Witness module should parse to original witness values"
    );
});
