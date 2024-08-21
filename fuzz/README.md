# Fuzzing

## Run a target

Run a fuzz target indefinitely using the following command:

```bash
cargo fuzz run TARGET
```

You can pass arguments to the fuzzer after the `--`, such as a maximum length of 50 bytes or a restriction to use only ASCII bytes.

```bash
cargo fuzz run TARGET -- -max_len=50 -ascii_only=1
```

## Compute code coverage

Compute the code coverage of the corpus of a given target using the following command:

```bash
cargo fuzz coverage TARGET
```

Generate a human-readable HTML coverage report using a command as below. _The exact paths might differ depending on the target architecture._

The demangler `rustfilt` must be installed.

```bash
cargo cov -- show -Xdemangler=rustfilt target/x86_64-unknown-linux-gnu/coverage/x86_64-unknown-linux-gnu/release/TARGET -instr-profile=fuzz/coverage/TARGET/coverage.profdata -show-line-counts-or-regions -show-instantiations --format html --output-dir=OUTPUT_DIR -ignore-filename-regex="\.cargo"
```

More information is available in the [rustc book](https://doc.rust-lang.org/stable/rustc/instrument-coverage.html#running-the-instrumented-binary-to-generate-raw-coverage-profiling-data).
