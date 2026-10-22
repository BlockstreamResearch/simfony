use crate::error::Error;
use crate::parse::{ParseFromStr, TypeAlias};

#[test]
fn test_reject_redefined_builtin_type() {
    let ty = TypeAlias::parse_from_str("type Ctx8 = u32")
        .expect_err("Redefining built-in alias should be rejected");

    assert!(ty
        .error()
        .to_string()
        .contains("Type alias `Ctx8` is already exists as built-in alias"));
}

#[test]
fn test_fragment_rejects_version_directive() {
    let err = TypeAlias::parse_from_str("simc \"*\"; type Ctx8 = u32")
        .expect_err("a version directive must not be accepted in a fragment");

    assert!(matches!(err.error(), Error::ReservedSimcKeyword));
}
