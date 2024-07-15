use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::ast;
use crate::error::Error;
use crate::parse::WitnessName;
use crate::value::TypedValue;

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
