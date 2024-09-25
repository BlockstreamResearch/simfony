use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::fmt;

use serde::{de, Deserialize, Deserializer};

use crate::ast;
use crate::error::{Error, RichError, WithFile, WithSpan};
use crate::parse::ParseFromStr;
use crate::str::WitnessName;
use crate::types::{AliasedType, ResolvedType};
use crate::value::Value;

/// Mapping of witness names to their assigned values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WitnessValues(BTreeMap<WitnessName, Value>);

impl WitnessValues {
    /// Return the empty witness map.
    pub fn empty() -> Self {
        Self(BTreeMap::new())
    }

    /// Get the value that is assigned to the given name.
    pub fn get(&self, name: &WitnessName) -> Option<&Value> {
        self.0.get(name)
    }

    /// Assign a `value` to the given `name`.
    ///
    /// ## Errors
    ///
    /// There is already a value assigned to this `name`.
    pub fn insert(&mut self, name: WitnessName, value: Value) -> Result<(), Error> {
        match self.0.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::WitnessReassigned(name)),
            Entry::Vacant(entry) => {
                entry.insert(value);
                Ok(())
            }
        }
    }

    /// Check if the witness values are consistent with the witness types as declared in the program.
    ///
    /// 1. Values that occur in the program are type checked.
    /// 2. Values that don't occur in the program are skipped.
    ///    The witness map may contain more values than necessary.
    ///
    /// There may be witnesses that are referenced in the program that are not assigned a value
    /// in the witness map. These witnesses may lie on pruned branches that will not be part of the
    /// finalized Simplicity program. However, before the finalization, we cannot know which
    /// witnesses will be pruned and which won't be pruned. This check skips unassigned witnesses.
    pub fn is_consistent(&self, program: &ast::Program) -> Result<(), Error> {
        let declared = program.witnesses();
        for name in self.0.keys() {
            let declared_ty = match declared.get(name) {
                Some(ty) => ty,
                None => continue,
            };
            let assigned_ty = self.0[name].ty();
            if assigned_ty != declared_ty {
                return Err(Error::WitnessTypeMismatch(
                    name.clone(),
                    declared_ty.clone(),
                    assigned_ty.clone(),
                ));
            }
        }

        Ok(())
    }

    /// Create an iterator over all name-value pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&WitnessName, &Value)> {
        self.0.iter()
    }
}

impl IntoIterator for WitnessValues {
    type Item = (WitnessName, Value);
    type IntoIter = <BTreeMap<WitnessName, Value> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl ParseFromStr for ResolvedType {
    fn parse_from_str(s: &str) -> Result<Self, RichError> {
        let aliased = AliasedType::parse_from_str(s)?;
        aliased
            .resolve_builtin()
            .map_err(Error::UndefinedAlias)
            .with_span(s)
            .with_file(s)
    }
}

struct WitnessMapVisitor;

impl<'de> de::Visitor<'de> for WitnessMapVisitor {
    type Value = WitnessValues;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a map with string keys and value-map values")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        let mut witness = WitnessValues::empty();
        while let Some((key, value)) = access.next_entry()? {
            witness.insert(key, value).map_err(de::Error::custom)?;
        }
        Ok(witness)
    }
}

impl<'de> Deserialize<'de> for WitnessValues {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(WitnessMapVisitor)
    }
}

struct ValueMapVisitor;

impl<'de> de::Visitor<'de> for ValueMapVisitor {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a map with \"value\" and \"type\" fields")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        let mut value = None;
        let mut ty = None;

        while let Some(key) = access.next_key::<&str>()? {
            match key {
                "value" => {
                    if value.is_some() {
                        return Err(de::Error::duplicate_field("value"));
                    }
                    value = Some(access.next_value::<&str>()?);
                }
                "type" => {
                    if ty.is_some() {
                        return Err(de::Error::duplicate_field("type"));
                    }
                    ty = Some(access.next_value::<&str>()?);
                }
                _ => {
                    return Err(de::Error::unknown_field(key, &["value", "type"]));
                }
            }
        }

        let ty = match ty {
            Some(s) => ResolvedType::parse_from_str(s).map_err(de::Error::custom)?,
            None => return Err(de::Error::missing_field("type")),
        };
        match value {
            Some(s) => Value::parse_from_str(s, &ty).map_err(de::Error::custom),
            None => Err(de::Error::missing_field("value")),
        }
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(ValueMapVisitor)
    }
}

struct ParserVisitor<A>(std::marker::PhantomData<A>);

impl<'de, A: ParseFromStr> de::Visitor<'de> for ParserVisitor<A> {
    type Value = A;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a valid string")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        A::parse_from_str(value).map_err(E::custom)
    }
}

impl<'de> Deserialize<'de> for WitnessName {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(ParserVisitor::<Self>(std::marker::PhantomData))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use crate::value::ValueConstructible;

    #[test]
    fn witness_reuse() {
        let s = r#"fn main() {
    let a: u32 = witness("a");
    let also_a: u32 = witness("a");
    assert!(jet::eq_32(a, b));
}"#;
        let program = parse::Program::parse_from_str(s).expect("parsing works");
        match ast::Program::analyze(&program).map_err(Error::from) {
            Ok(_) => panic!("Witness reuse was falsely accepted"),
            Err(Error::WitnessReused(..)) => {}
            Err(error) => panic!("Unexpected error: {error}"),
        }
    }

    #[test]
    fn witness_type_mismatch() {
        let s = r#"fn main() {
    let a: u32 = witness("a");
    assert!(jet::is_zero_32(a));
}"#;

        let mut witness = WitnessValues::empty();
        let a = WitnessName::parse_from_str("a").unwrap();
        witness.insert(a, Value::u16(42)).unwrap();

        match crate::satisfy(s, &witness) {
            Ok(_) => panic!("Ill-typed witness assignment was falsely accepted"),
            Err(error) => assert_eq!(
                "Witness `a` was declared with type `u32` but its assigned value is of type `u16`",
                error
            ),
        }
    }

    #[test]
    fn witness_duplicate_assignment() {
        let mut witness = WitnessValues::empty();
        let a = WitnessName::parse_from_str("a").unwrap();
        witness.insert(a.clone(), Value::u32(42)).unwrap();
        match witness.insert(a, Value::u32(43)) {
            Ok(_) => panic!("Duplicate witness assignment was falsely accepted"),
            Err(Error::WitnessReassigned(..)) => {}
            Err(error) => panic!("Unexpected error: {error}"),
        }
    }

    #[test]
    fn witness_serde_duplicate_assignment() {
        let s = r#"{
  "a": { "value": "42", "type": "u32" },
  "a": { "value": "43", "type": "u16" }
}"#;

        match serde_json::from_str::<WitnessValues>(s) {
            Ok(_) => panic!("Duplicate witness assignment was falsely accepted"),
            Err(error) => assert_eq!(
                "Witness `a` has already been assigned a value at line 4 column 1",
                &error.to_string()
            ),
        }
    }

    #[test]
    fn witness_outside_main() {
        let s = r#"fn f() -> u32 {
    witness("output_of_f")
}

fn main() {
    assert!(jet::is_zero_32(f()));
}"#;

        match crate::compile(s) {
            Ok(_) => panic!("Witness outside main was falsely accepted"),
            Err(error) => {
                assert!(error
                    .contains("Witness expressions are not allowed outside the `main` function"))
            }
        }
    }
}
