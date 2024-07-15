use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;

use serde::{de, Deserialize, Deserializer};

use crate::error::{Error, RichError, WithFile, WithSpan};
use crate::parse::{ParseFromStr, WitnessName};
use crate::types::{AliasedType, ResolvedType};
use crate::value::TypedValue;
use crate::{ast, parse};

/// Mapping of witness names to their assigned values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WitnessValues(HashMap<WitnessName, TypedValue>);

impl WitnessValues {
    /// Return the empty witness map.
    pub fn empty() -> Self {
        Self(HashMap::new())
    }

    /// Get the value that is assigned to the given name.
    pub fn get(&self, name: &WitnessName) -> Option<&TypedValue> {
        self.0.get(name)
    }

    /// Assign a `value` to the given `name`.
    ///
    /// ## Errors
    ///
    /// There is already a value assigned to this `name`.
    pub fn insert(&mut self, name: WitnessName, value: TypedValue) -> Result<(), Error> {
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
    type Value = TypedValue;

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
        let expression = match value {
            Some(s) => parse::Expression::parse_from_str(s).map_err(de::Error::custom)?,
            None => return Err(de::Error::missing_field("value")),
        };

        TypedValue::from_const_expr(&expression, &ty).map_err(de::Error::custom)
    }
}

impl<'de> Deserialize<'de> for TypedValue {
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
