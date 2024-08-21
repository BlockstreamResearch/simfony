#![no_main]

use libfuzzer_sys::{fuzz_target, Corpus};

/// The PEST parser is slow for inputs with many open brackets.
/// Detect some of these inputs to reject them from the corpus.
///
/// ```text
/// fn n(){ { (s,(( (Ns,(s,(x,(((s,((s,(s,(s,(x,(( {5
/// ```
fn slow_input(program_text: &str) -> bool {
    let mut consecutive_open_brackets = 0;

    for c in program_text.chars() {
        if c == '(' || c == '[' || c == '{' {
            consecutive_open_brackets += 1;
            if consecutive_open_brackets > 3 {
                return true;
            }
        } else if !c.is_whitespace() {
            consecutive_open_brackets = 0;
        }
    }

    false
}

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(program_text) = core::str::from_utf8(data) {
        if slow_input(program_text) {
            return Corpus::Reject;
        }

        let _ = simfony::compile(program_text);
    }

    Corpus::Keep
});
