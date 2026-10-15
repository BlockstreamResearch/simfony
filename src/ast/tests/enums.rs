use crate::ast::ElementsJetHinter;
use crate::{TemplateAst, UnstableFeatures};

use super::analyze;

#[test]
fn enum_declaration_registers_type_alias() {
    let result = analyze(
        "enum Color { Red, Green }
            fn main() { let _x: Color = witness::C; }",
    );
    assert!(
        result.is_ok(),
        "enum name should resolve as a type: {result:?}"
    );
}

#[test]
fn enum_duplicate_variant_name_is_error() {
    let result = analyze("enum Color { Red, Red }\nfn main() {}");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("duplicate variant name"));
}

#[test]
fn enum_variant_named_after_builtin_pattern_is_ok() {
    // The written `Enum::Variant` form keeps `Action::None` distinct
    // from the built-in option literal, so variant names are
    // unrestricted.
    let result = analyze(
        "enum Action { None, Some, Other, }
            fn main() {
                match witness::W {
                    Action::None => {},
                    Action::Some => {},
                    Action::Other => {},
                }
            }",
    );

    assert!(
        result.is_ok(),
        "builtin-named variants should work: {result:?}"
    );
}

#[test]
fn enum_empty_is_error() {
    let result = analyze("enum Color { }\nfn main() {}");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("at least one variant"));
}

#[test]
fn enum_duplicate_name_is_error() {
    let result = analyze(
        "enum Color { Red, Green }
            enum Color { Blue, Cyan }
            fn main() {}",
    );

    assert!(result.is_err(), "redefined enum name should error");
}

#[test]
fn enum_declaration_inside_module_errors() {
    // FIXME: Enums may only be declared at the top level of a file.
    let result = analyze(
        "mod m {
                pub enum Choice { X, Y, }
            }
            fn main() {}",
    );

    let err = result.expect_err("enum inside `mod` must be rejected");
    assert!(
        err.contains("top level"),
        "error should say enums are top-level only: {err}"
    );
}

#[test]
fn enum_declaration_in_dependency_errors() {
    use crate::ast::tests::analyze_multifile;

    // FIXME: An enum's declared name is its identity in the ABI, so enums may only be declared in the program's own files.
    let result = analyze_multifile(vec![
        (
            "main.simf",
            "use lib::A::helper;
            fn main() { helper(); }",
        ),
        (
            "libs/lib/A.simf",
            "pub enum Status { On, Off, } pub fn helper() {}",
        ),
    ]);

    let err = result.expect_err("enums in dependency files must be rejected");
    assert!(
        err.contains("dependency"),
        "error should say enums cannot live in dependency files: {err}"
    );
}

#[test]
fn enum_payload_match_binds_payload() {
    let result = analyze(
        "enum Action { Refresh(u32, bool), Cold, }
            fn main() {
                match witness::W {
                    Action::Refresh(n: u32, b: bool) => {
                        assert!(jet::is_zero_32(n));
                        assert!(b);
                    },
                    Action::Cold => {},
                }
            }",
    );

    assert!(
        result.is_ok(),
        "payload bindings should analyze: {result:?}"
    );
}

#[test]
fn enum_payload_binding_type_mismatch_is_error() {
    let result = analyze(
        "enum Action { Refresh(u32), Cold, }
            fn main() {
                match witness::W {
                    Action::Refresh(n: u16) => { assert!(jet::is_zero_16(n)); },
                    Action::Cold => {},
                }
            }",
    );

    assert!(
        result.is_err(),
        "binding type must equal the declared payload type"
    );
}

#[test]
fn enum_payload_binding_arity_mismatch_is_error() {
    let result = analyze(
        "enum Action { Refresh(u32, bool), Cold, }
            fn main() {
                match witness::W {
                    Action::Refresh(n: u32) => { assert!(jet::is_zero_32(n)); },
                    Action::Cold => {},
                }
            }",
    );

    assert!(result.is_err());
    assert!(
        result.unwrap_err().contains("payload value"),
        "error should describe the arity mismatch"
    );
}

#[test]
fn enum_single_variant_matches() {
    // A single-variant enum is a named unit type; its match has one arm.
    let result = analyze(
        "enum Marker { Only }
            fn main() {
                match witness::M {
                    Marker::Only => {},
                }
            }",
    );

    assert!(
        result.is_ok(),
        "single-variant enum should work: {result:?}"
    );
}

#[test]
fn enum_match_undefined_enum_is_error() {
    let result = analyze(
        "fn main() {
                match witness::P {
                    Unknown::A => {},
                    Unknown::B => {},
                }
            }",
    );

    assert!(result.is_err(), "undefined enum should error");
}

#[test]
fn enum_match_mixed_enum_names_is_error() {
    let result = analyze(
        "enum A { X, Y }
            enum B { P, Q }

            fn main() {
                match witness::W {
                    A::X => {},
                    B::Q => {},
                }
            }",
    );

    assert!(result.is_err());
    assert!(result.unwrap_err().contains("same enum"));
}

#[test]
fn enum_match_unknown_variant_is_error() {
    let result = analyze(
        "enum A { X, Y }
            fn main() {
                match witness::W {
                    A::X => {},
                    A::Z => {},
                }
            }",
    );

    assert!(result.is_err());
    assert!(result.unwrap_err().contains("not defined"));
}

#[test]
fn enum_match_duplicate_arm_is_error() {
    let result = analyze(
        "enum A { X, Y }
            fn main() {
                match witness::W {
                    A::X => {},
                    A::X => {},
                    A::Y => {},
                }
            }",
    );

    assert!(result.is_err());
    assert!(result.unwrap_err().contains("duplicate arm"));
}

#[test]
fn enum_match_missing_arm_is_error() {
    let result = analyze(
        "enum A { X, Y, Z }
            fn main() {
                match witness::W {
                    A::X => {},
                    A::Y => {},
                }
            }",
    );

    assert!(result.is_err());
    assert!(result.unwrap_err().contains("must cover all 3 variants"));
}

#[test]
fn enum_match_rejects_scrutinee_of_different_enum() {
    let result = analyze(
        "enum A { X, Y, }
            enum B { P, Q, }

            fn main() {
                let v: A = witness::V;
                match v {
                    B::P => {},
                    B::Q => {},
                }
            }",
    );

    assert!(
        result.is_err(),
        "matching a value of enum A against B's variants must be a type error"
    );
}

#[test]
fn enum_match_rejects_plain_u8_scrutinee() {
    let result = analyze(
        "enum Action { A, B, }
            fn main() {
                let v: u8 = witness::V;
                match v {
                    Action::A => {},
                    Action::B => {},
                }
            }",
    );

    assert!(
        result.is_err(),
        "matching a u8 against enum variants must be a type error"
    );
}

#[test]
fn enum_match_rejects_same_shaped_enum() {
    // Identity is the declaration site: two enums with the same variants
    // are distinct types, so their values are not interchangeable.
    let result = analyze(
        "enum AChoice { X, Y, }
            enum BChoice { X, Y, }

            fn main() {
                let v: AChoice = witness::V;
                match v {
                    BChoice::X => {},
                    BChoice::Y => {},
                }
            }",
    );

    assert!(
        result.is_err(),
        "structurally identical enums must not be interchangeable"
    );
}

#[test]
fn enum_match_on_non_enum_alias_is_error() {
    let result = analyze(
        "type Foo = u32;
            fn main() {
                match witness::W {
                    Foo::A => {},
                    Foo::B => {},
                }
            }",
    );

    assert!(result.is_err());
    assert!(
        result.unwrap_err().contains("not an enum"),
        "a defined non-enum alias should not report an undefined alias"
    );
}

#[test]
fn enum_cast_to_same_shaped_enum_is_rejected() {
    // Casts prove structural equality, but enums are nominal: a cast
    // between same-shaped enums would map variants by ordinal position
    // (Source::Allow -> Target::Deny), silently reversing semantics.
    let result = analyze(
        "enum Source { Allow, Deny, }
            enum Target { Deny, Allow, }

            fn main() {
                let s: Source = Source::Allow;
                let _t: Target = <Source>::into(s);
            }",
    );

    assert!(
        result.is_err(),
        "same-shaped enums must not cast into each other"
    );
}

#[test]
fn enum_cast_to_structural_sum_is_rejected() {
    let result = analyze(
        "enum Source { Allow, Deny, }
            fn main() {
                let s: Source = Source::Allow;
                let _e: Either<(), ()> = <Source>::into(s);
            }",
    );
    assert!(
        result.is_err(),
        "an enum must not cast to its structural sum"
    );

    let result = analyze(
        "enum Source { Allow, Deny, }
            fn main() {
                let e: Either<(), ()> = Left(());
                let _s: Source = <Either<(), ()>>::into(e);
            }",
    );
    assert!(result.is_err(), "a structural sum must not cast to an enum");
}

#[test]
fn enum_cast_reshaping_enum_free_siblings_is_ok() {
    // Enum-free structure may reshape around an enum that stays put
    // at its position.
    let result = analyze(
        "enum E { A, B, }
            fn main() {
                let x: (E, (u16, u16)) = (E::A, (1, 2));
                let _y: (E, u32) = <(E, (u16, u16))>::into(x);
            }",
    );

    assert!(
        result.is_ok(),
        "reshaping enum-free siblings must stay castable: {result:?}"
    );
}

#[test]
fn enum_cast_reshaping_enum_free_siblings_is_ok_2() {
    // This one has an enum with a left sibling which is much bigger (as a HL type DAG) in the
    // source type than the target.
    let result = analyze(
        "enum E { A, B, }
            fn main() {
                let x: ((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)
                    = ((Left(()), Left(()), Left(())), E::A);
                let _y: ((Option<u8>, Option<u8>, Option<u8>), E)
                    = <((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)>::into(x);
            }",
    );
    assert!(
        result.is_ok(),
        "reshaping enum-free siblings must stay castable: {result:?}"
    );

    // Same thing, but we try to swap out the enums. This should fail.
    let result = analyze(
        "enum E { A, B, }
            enum F { C, D, }

            fn main() {
                let x: ((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)
                    = ((Left(()), Left(()), Left(())), E::A);

                let _y: ((Option<u8>, Option<u8>, Option<u8>), F)
                    = <((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)>::into(x);
            }",
    );
    assert!(
        result.is_err(),
        "reshaping enum-free siblings must stay non-castable: {result:?}"
    );
}

#[test]
fn enum_cast_to_itself_is_ok() {
    let result = analyze(
        "enum Source { Allow, Deny, }
            fn main() {
                let s: Source = Source::Allow;
                let _t: Source = <Source>::into(s);
            }",
    );

    assert!(
        result.is_ok(),
        "nominally identical cast should stay allowed: {result:?}"
    );
}

#[test]
fn enum_cast_option_either() {
    let result = analyze(
        "enum E { A, B, }
            fn main() {
                let x: Option<E> = None;
                let _y: Either<(), E> = <Option<E>>::into(x);
            }",
    );
    result.expect_err("this should work");
}

#[test]
fn enum_cast_array_tuple() {
    let result = analyze(
        "enum E { A, B, }
            fn main() {
                let x: [E; 2] = [E::A, E::B];
                let _y: (E, E) = <[E; 2]>::into(x);
            }",
    );
    result.expect_err("this should work");
}

#[test]
fn enum_cast_list1_option() {
    let result = analyze(
        "enum E { A, B, }
            fn main() {
                let x: List<E, 2> = list![];
                let _y: Option<E> = <List<E, 2>>::into(x);
            }",
    );
    result.expect_err("this should work");
}

#[test]
fn enum_cast_list2_option() {
    let result = analyze(
        "enum E { A, B, }
            fn main() {
                let x: List<E, 4> = list![];
                let _y: (Option<(E, E)>, Option<E>) = <List<E, 4>>::into(x);
            }",
    );
    result.expect_err("this should work");
}

#[test]
fn enum_named_after_builtin_type_is_rejected() {
    // `enum Signature` would shadow the built-in alias: constructions
    // would name the enum while type annotations resolve to the
    // builtin, and the ABI would report the bare name ambiguously.
    for name in crate::str::ALIAS_RESERVED {
        let result = analyze(&format!("enum {name} {{ A, B, }}\nfn main() {{}}"));
        assert!(result.is_err(), "enum named `{name}` must be rejected");
    }
}

#[test]
fn enum_alias_named_after_pattern_is_matchable() {
    // `type Left = Action` shadows a built-in pattern name; the arm
    // parser distinguishes `Left::A` (enum path) from `Left(x)`
    // (built-in pattern) by the `::` that follows.
    let result = analyze(
        "enum Action { A, B, }
            type Left = Action;

            fn main() {
                let v: Left = Action::A;
                match v {
                    Left::A => {},
                    Left::B => {},
                }
            }",
    );
    assert!(
        result.is_ok(),
        "an enum alias shadowing a pattern name must be matchable: {result:?}"
    );
}

#[test]
fn enum_alias_named_none_is_constructable() {
    // The nullary built-in `None` parses without parentheses, so the
    // expression parser must yield to enum construction when `::`
    // follows, like the arm parser does.
    let result = analyze(
        "enum Action { A, B, }
            type None = Action;

            fn main() {
                let _x: None = None::A;
            }",
    );

    assert!(
        result.is_ok(),
        "`None::A` must parse as enum construction: {result:?}"
    );
}

#[test]
fn alias_named_after_pattern_stays_valid_without_enums() {
    // Stable programs may alias pattern names; the enums feature must
    // not retroactively reject them.
    let result = TemplateAst::new_with_unstable(
        "type Left = u32;\nfn main() { let _x: Left = 1; }",
        &UnstableFeatures::none(),
        Box::new(ElementsJetHinter::new()),
    );
    assert!(
        result.is_ok(),
        "stable alias names must stay valid without -Z enums"
    );
}

#[test]
fn enum_construction_follows_lexical_scope_in_source() {
    // Inside a module the root's `E` is not in scope: only the local
    // import name may construct, exactly as matches require. The
    // declared-name fallback applies only to witness/argument files.
    let result = analyze(
        "pub enum E { A, B, }
            mod m {
                use crate::E as Choice;
                pub fn make() -> Choice {
                    E::A
                }
            }

            use crate::m::make;
            fn main() {
                let _x: E = make();
            }",
    );
    assert!(
        result.is_err(),
        "an out-of-scope declared name must not construct"
    );

    let result = analyze(
        "pub enum E { A, B, }
            mod m {
                use crate::E as Choice;
                pub fn make() -> Choice {
                    Choice::A
                }
            }

            use crate::m::make;
            fn main() {
                let _x: E = make();
            }",
    );
    assert!(
        result.is_ok(),
        "the imported alias must construct: {result:?}"
    );
}

#[test]
fn enum_requires_unstable_feature() {
    let result = TemplateAst::new_with_unstable(
        "enum Color { Red, Green }\nfn main() {}",
        &UnstableFeatures::none(),
        Box::new(ElementsJetHinter::new()),
    );
    assert!(result.is_err(), "enum syntax is gated behind -Z enums");
}
