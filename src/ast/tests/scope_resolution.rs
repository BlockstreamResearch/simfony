use super::{analyze, analyze_multifile};

#[test]
fn duplicate_function_parameter_is_rejected() {
    let err = analyze(
        "fn f(a: u256, a: Pubkey) -> u256 { a }
            fn main() {
                let _: u256 = f(0, 1);
            }",
    )
    .unwrap_err();

    assert!(
        err.contains("Parameter `a` was defined multiple times"),
        "{err}"
    );
}

#[test]
fn private_type_alias_from_dependency_does_not_leak() {
    let result = analyze_multifile(vec![
        (
            "main.simf",
            "use lib::A::helper; fn main() { helper(); let x: Secret = 0; }",
        ),
        ("libs/lib/A.simf", "type Secret = u32; pub fn helper() {}"),
    ]);

    assert!(
        result.is_err(),
        "private alias from another file leaked into root scope: {result:?}"
    );
}

#[test]
fn same_alias_name_in_different_modules_does_not_conflict_if_only_one_is_imported() {
    let result = analyze_multifile(vec![
        (
            "main.simf",
            "use lib::A::Word; use lib::B::id; fn main() { let x: Word = 0; assert!(jet::is_zero_32(id(x))); }",
        ),
        ("libs/lib/A.simf", "pub type Word = u32;"),
        ("libs/lib/B.simf", "pub type Word = u16; pub fn id(x: u32) -> u32 { x }"),
    ]);

    assert!(
        result.is_ok(),
        "unimported alias from another module should not collide: {result:?}"
    );
}

#[test]
fn main_must_be_defined_once_per_project() {
    let result = analyze_multifile(vec![
        ("main.simf", "use lib::A::helper; fn main() { helper(); }"),
        ("libs/lib/A.simf", "fn main() {} pub fn helper() {}"),
    ]);

    assert!(
        result.is_err(),
        "Main function must be inside an entry file: {result:?}"
    );
}

#[test]
fn test_local_definitions_visibility() {
    // main.simf defines a private function and a public function.
    // Expected: Both should be usable locally in main.
    let result = analyze_multifile(vec![(
        "main.simf",
        "fn private_fn() {} pub fn public_fn() {} fn main() { private_fn(); public_fn(); }",
    )]);

    assert!(
        result.is_ok(),
        "Local definitions should be visible: {result:?}"
    );
}

#[test]
fn test_pub_use_propagation() {
    // Scenario: Re-exporting.
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn foo() {}"),
        ("libs/lib/B.simf", "pub use crate::A::foo;"),
        ("main.simf", "use lib::B::foo; fn main() { foo(); }"),
    ]);

    assert!(
        result.is_ok(),
        "Public re-exports must be visible: {result:?}"
    );
}

#[test]
fn test_private_import_encapsulation_error() {
    // Scenario: A private import cannot be re-exported.
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn foo() {}"),
        ("libs/lib/B.simf", "use crate::A::foo;"), // <--- Private binding!
        ("main.simf", "use lib::B::foo; fn main() {}"),
    ]);

    let err = result.expect_err("Private imports should not be accessible");
    assert!(err.contains("private") || err.contains("foo"));
}

#[test]
fn test_separated_type_aliases_and_functions() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub type bar = u32; pub fn bar() {}"),
        (
            "main.simf",
            "use lib::A::bar; fn main() { bar(); let x: bar = 0; }",
        ),
    ]);

    assert!(
        result.is_ok(),
        "AST should support separate namespaces for types and functions: {result:?}"
    );
}

#[test]
fn test_public_main_is_forbidden() {
    let result = analyze_multifile(vec![("main.simf", "pub fn main() {}")]);

    let err = result.expect_err("Public main should be rejected");
    assert!(err.contains("Main") && err.contains("public"));
}

#[test]
fn test_aliasing_to_main_is_forbidden() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub type bar = u32;"),
        ("main.simf", "use lib::A::bar as main; fn main() {}"),
    ]);

    let err = result.expect_err("Aliasing to main should be rejected");
    assert!(err.contains("Main") && err.contains("alias"));
}

#[test]
fn test_renaming_with_use() {
    // Expected: "bar" is usable, "foo" is not.
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn foo() {}"),
        (
            "main.simf",
            "use lib::A::foo as bar; fn main() { bar(); foo(); }",
        ),
    ]);

    let err = result.expect_err("Using the original unaliased name 'foo' should fail");
    assert!(err.contains("foo") && (err.contains("not defined") || err.contains("unresolved")));
}

#[test]
fn test_multiple_aliases_in_list() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn foo() {} pub fn baz() {}"),
        (
            "main.simf",
            "use lib::A::{foo as bar, baz as qux}; fn main() { bar(); qux(); }",
        ),
    ]);

    assert!(
        result.is_ok(),
        "List aliases should be resolvable: {result:?}"
    );
}

#[test]
fn test_alias_private_item_fails() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "fn secret() {}"),
        ("main.simf", "use lib::A::secret as my_secret; fn main() {}"),
    ]);

    let err = result.expect_err("Aliasing a private item should fail");
    assert!(err.contains("secret") && err.contains("private"));
}

#[test]
fn test_deep_reexport_with_aliases() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn original() {}"),
        ("libs/lib/B.simf", "pub use crate::A::original as middle;"),
        (
            "main.simf",
            "use lib::B::middle as final_name; fn main() { final_name(); }",
        ),
    ]);

    assert!(
        result.is_ok(),
        "Deep alias re-exports should work: {result:?}"
    );
}

#[test]
fn test_deep_reexport_private_link_fails() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn target() {}"),
        ("libs/lib/B.simf", "use crate::A::target as hidden_alias;"),
        ("main.simf", "use lib::B::hidden_alias; fn main() {}"),
    ]);

    let err = result.expect_err("Private intermediate aliases should block resolution");
    assert!(err.contains("hidden_alias") && err.contains("private"));
}

#[test]
fn test_plain_import_and_alias_to_same_name_is_rejected() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn foo() {}"),
        ("libs/lib/B.simf", "pub fn foo() {}"),
        (
            "main.simf",
            "use lib::A::foo; use lib::B::foo as foo; fn main() {}",
        ),
    ]);

    let err = result.expect_err("Duplicate names in scope should fail");
    assert!(err.contains("foo") && err.contains("multiple times"));
}

#[test]
fn test_alias_cannot_reuse_local_definition_name() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn bar() {}"),
        (
            "main.simf",
            "pub fn foo() {} use lib::A::bar as foo; fn main() {}",
        ),
    ]);

    let err = result.expect_err("Alias reusing a local name should fail");
    assert!(err.contains("foo") && err.contains("multiple times"));
}

#[test]
#[ignore = "Pending better error handler:private item errors currently mask duplicate imports"]
fn test_private_alias_error_does_not_mask_duplicate_function_import() {
    // Scenario: Loading a private item fails, but we must STILL catch if a
    // secondary import tries to bind to the same name.
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn foo() {}"),
        ("libs/lib/B.simf", "pub fn foo() {} type foo = u32;"),
        (
            "main.simf",
            "use lib::A::foo; use lib::B::foo; fn main() {}",
        ),
    ]);

    let err = result.expect_err("Duplicate function import should fail");

    // It shouldn't just complain about the private type `foo`; it must also
    // complain that `foo` was imported twice!
    assert!(err.contains("foo") && err.contains("multiple times"));
}

#[test]
fn test_failed_alias_import_does_not_poison_following_imports() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn nope() {}"),
        ("libs/lib/B.simf", "pub fn bar() {}"),
        (
            "main.simf",
            "use lib::A::missing as foo; use lib::B::bar as foo; fn main() {}",
        ),
    ]);

    let err = result.expect_err("Build should fail on the unresolved import");

    // It should complain about `missing`, but NOT about `foo` being duplicated,
    // because the first import failed and never actually reserved the name `foo`.
    assert!(err.contains("missing") || err.contains("not found"));
    assert!(!err.contains("multiple times"));
}

#[test]
fn test_local_function_cannot_reuse_alias_name() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub fn bar() {}"),
        (
            "main.simf",
            "use lib::A::bar as foo; pub fn foo() {} fn main() {}",
        ),
    ]);

    let err = result.expect_err("Build should fail when a local definition reuses an alias name");
    assert!(err.contains("foo") && err.contains("multiple times"));
}

#[test]
fn test_local_type_alias_cannot_reuse_alias_name() {
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub type bar = u32;"),
        (
            "main.simf",
            "use lib::A::bar as foo; type foo = u64; fn main() {}",
        ),
    ]);

    let err = result.expect_err("Build should fail when a local definition reuses an alias name");
    assert!(err.contains("foo") && err.contains("multiple times"));
}
