use super::analyze;

#[test]
fn const_with_undefined_type_reports_only_the_type() {
    let err = analyze("const A: Missing = (1, 2); fn main() {}").unwrap_err();
    assert!(err.contains("Missing"), "{err}");
    assert!(!err.contains("cannot be evaluated"), "{err}");
}

#[test]
fn private_const_cannot_be_imported() {
    let err = analyze("mod m { const A: u8 = 1; } use crate::m::A; fn main() {}").unwrap_err();
    assert!(err.contains("private"), "{err}");
}
