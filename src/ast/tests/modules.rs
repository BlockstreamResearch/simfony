use super::analyze_multifile;

#[test]
fn test_public_nested_modules_are_accessible() {
    let result = analyze_multifile(vec![
        (
            "libs/lib/A.simf",
            "pub mod outer { pub mod inner { pub fn target() {} } }",
        ),
        (
            "main.simf",
            "use lib::A::outer::inner::target; fn main() {}",
        ),
    ]);

    assert!(
        result.is_ok(),
        "Deeply nested public modules should be accessible: {result:?}"
    );
}

#[test]
fn test_private_inner_module_blocks_external_access() {
    let result = analyze_multifile(vec![
        // `outer` is public, but `inner` is private
        // Even though `target` is public, the private wall at `inner` blocks it.
        (
            "libs/lib/A.simf",
            "pub mod outer { mod inner { pub fn target() {} } }",
        ),
        (
            "main.simf",
            "use lib::A::outer::inner::target; fn main() {}",
        ),
    ]);

    let err = result.expect_err("Private inner module must block access");
    assert!(err.contains("inner") && err.contains("private"));
}

#[test]
#[ignore = "Not implemented now"]
fn test_importing_a_whole_module_allows_path_traversal() {
    // Scenario: Instead of importing the function, the user imports the module itself,
    // and then uses the module name as a prefix.
    let result = analyze_multifile(vec![
        ("libs/lib/A.simf", "pub mod math { pub fn add() {} }"),
        ("main.simf", "use lib::A::math; fn main() { math::add(); }"),
    ]);

    assert!(
        result.is_ok(),
        "Importing a module should bring its namespace into scope: {result:?}"
    );
}

#[test]
fn test_duplicate_module_blocks_are_rejected() {
    let result = analyze_multifile(vec![(
        "main.simf",
        "mod inner {} mod inner {} fn main() {}",
    )]);

    let err = result.expect_err("Duplicate mod blocks must fail");
    assert!(err.contains("inner") && err.contains("multiple times"));
}

#[test]
fn test_sibling_modules_can_access_each_others_public_items() {
    // In Rust, sibling modules share the same parent, so they are allowed to see
    // each other (even if they are private to the outside world).
    let result = analyze_multifile(vec![(
        "main.simf",
        "
                mod brother { pub fn toy() {} }
                mod sister { use crate::brother::toy; }
                fn main() {}
            ",
    )]);

    assert!(
        result.is_ok(),
        "Sibling modules should be able to import from each other: {result:?}"
    );
}

#[test]
fn test_inline_module_can_import_global_item() {
    // Scenario: A nested module needs to access a function defined at the very top of the file.
    // This proves `crate::` correctly points to the un-wrapped MAIN_MODULE root.
    let result = analyze_multifile(vec![(
        "main.simf",
        "
                pub fn global_func() {}
                mod inner {
                    use crate::global_func;
                    pub fn call_it() { global_func(); }
                }
                fn main() {}
            ",
    )]);

    assert!(
        result.is_ok(),
        "Nested modules must be able to import global items: {result:?}"
    );
}

#[test]
fn test_deeply_nested_inline_modules() {
    // Scenario: Traversing multiple inline module boundaries.
    let result = analyze_multifile(vec![(
        "main.simf",
        "
                mod level1 {
                    pub mod level2 {
                        pub fn treasure() {}
                    }
                }
                mod explorer {
                    use crate::level1::level2::treasure;
                }
                fn main() {}
            ",
    )]);

    assert!(
        result.is_ok(),
        "Deeply nested inline modules must resolve correctly: {result:?}"
    );
}

#[test]
fn test_inline_module_privacy_is_enforced_between_siblings() {
    // Scenario: Sibling modules can see each other, but they CANNOT see each other's PRIVATE items.
    let result = analyze_multifile(vec![(
        "main.simf",
        "
                mod brother {
                    fn secret_toy() {} // Missing 'pub'
                }
                mod sister {
                    use crate::brother::secret_toy;
                }
                fn main() {}
            ",
    )]);

    let err = result.expect_err("Private inline items must remain hidden from siblings");
    assert!(err.contains("secret_toy") && err.contains("private"));
}

#[test]
fn test_main_scope_cannot_access_private_inline_items() {
    // Scenario: The root of the file tries to import a private item from its own child module.
    let result = analyze_multifile(vec![(
        "main.simf",
        "
                mod child {
                    fn hidden() {}
                }
                use crate::child::hidden;
                fn main() {}
            ",
    )]);

    let err = result.expect_err("The root file scope must respect inline module privacy");
    assert!(err.contains("hidden") && err.contains("private"));
}

#[test]
fn test_inline_module_alias_import() {
    // Scenario: Importing an item from a sibling inline module and renaming it locally.
    let result = analyze_multifile(vec![(
        "main.simf",
        "
                mod supplier {
                    pub fn raw_material() {}
                }
                mod factory {
                    use crate::supplier::raw_material as finished_product;
                    pub fn produce() { finished_product(); }
                }
                fn main() {}
            ",
    )]);

    assert!(
        result.is_ok(),
        "Inline imports must support aliasing: {result:?}"
    );
}
