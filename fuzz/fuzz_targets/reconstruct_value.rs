#![no_main]

use libfuzzer_sys::fuzz_target;

use simfony::value::{Value, StructuralValue};

fuzz_target!(|value: Value| {
    let structural_value = StructuralValue::from(&value);
    let reconstructed_value = Value::reconstruct(&structural_value, value.ty()).unwrap();
    assert_eq!(reconstructed_value, value);
});
