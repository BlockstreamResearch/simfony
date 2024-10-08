#![no_main]

use libfuzzer_sys::fuzz_target;

use simfony::value::Value;

fuzz_target!(|value: Value| {
    let value_string = value.to_string();
    let parsed_value = Value::parse_from_str(&value_string, value.ty())
        .expect("Value string should be parseable");
    assert_eq!(
        value, parsed_value,
        "Value string should parse to original value"
    );
});
