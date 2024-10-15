#![no_main]

use libfuzzer_sys::fuzz_target;

use simfony::WitnessValues;

fuzz_target!(|witness_values: WitnessValues| {
    let witness_text = serde_json::to_string(&witness_values)
        .expect("Witness map should be convertible into JSON");
    let parsed_witness_text =
        serde_json::from_str(&witness_text).expect("Witness JSON should be parseable");
    assert_eq!(
        witness_values, parsed_witness_text,
        "Witness JSON should parse to original witness map"
    );
});
