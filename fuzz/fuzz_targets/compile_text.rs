#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::{fuzz_target, Corpus};

use simfony::{ArbitraryOfType, Arguments};

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
    let mut u = arbitrary::Unstructured::new(data);

    let program_text = match <String>::arbitrary(&mut u) {
        Ok(x) => x,
        Err(..) => return Corpus::Reject,
    };
    if slow_input(&program_text) {
        return Corpus::Reject;
    }
    let template = match simfony::TemplateProgram::new(program_text) {
        Ok(x) => x,
        Err(..) => return Corpus::Keep,
    };
    let arguments = match Arguments::arbitrary_of_type(&mut u, template.parameters()) {
        Ok(arguments) => arguments,
        Err(..) => return Corpus::Reject,
    };
    let _ = template.instantiate(arguments, false);

    Corpus::Keep
});
