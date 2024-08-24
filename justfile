# Format code
fmt:
    cargo fmt --all

# Check if code is formatted
fmtcheck:
    cargo fmt --all -- --check

# Run code linter
lint:
    cargo clippy --all-targets --workspace -- --deny warnings

# Run unit tests
test:
    cargo test --workspace

# Check code (CI)
check:
    cargo --version
    rustc --version
    just fmtcheck
    just lint
    just test

# Run fuzz test for 30 seconds
fuzz target:
    cargo-fuzz run {{target}} -- -max_total_time=30 -max_len=50

# Check fuzz targets (CI; requires nightly)
check_fuzz:
    just fuzz display_parse_tree
    just fuzz compile_text
    just fuzz compile_parse_tree

# Remove all temporary files
clean:
    rm -rf target
    rm -rf fuzz/target
