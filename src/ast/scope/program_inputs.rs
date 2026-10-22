use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::sync::Arc;

use crate::ast::{Expression, Program};
use crate::debug::{CallTracker, TrackedCallName};
use crate::error::{Error, Span};
use crate::types::ResolvedType;
use crate::witness::{Parameters, WitnessTypes};
use crate::TemplateProgramWitness;

/// Everything the analyzed [`Program`] stores besides its `main` body.
#[derive(Default)]
pub(super) struct ProgramInputs {
    parameters: HashMap<TemplateProgramWitness, ResolvedType>,
    witnesses: HashMap<TemplateProgramWitness, ResolvedType>,
    call_tracker: CallTracker,
}

impl ProgramInputs {
    /// Insert a parameter into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::ExpressionTypeMismatch`] A parameter of the same name has already been defined as a different type.
    pub(super) fn insert_parameter(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        // A use with a broken type says nothing reliable about the parameter,
        // so the stored type never contains `!` and never changes once stored.
        if ty.contains_never() {
            return Ok(());
        }

        match self.parameters.entry(name.clone()) {
            Entry::Occupied(entry) if entry.get().same_as(&ty) => Ok(()),
            Entry::Occupied(entry) => Err(Error::ExpressionTypeMismatch {
                expected: entry.get().clone(),
                found: ty,
            }),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Insert a witness into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::WitnessReused`] A witness with the same name has already been defined.
    pub(super) fn insert_witness(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        match self.witnesses.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::WitnessReused { name }),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Track a call expression with its span.
    pub(super) fn track_call<S: AsRef<Span>>(&mut self, span: &S, name: TrackedCallName) {
        self.call_tracker.track_call(*span.as_ref(), name);
    }

    /// Build the analyzed program with the given `main` body.
    pub(super) fn into_program(self, main: Expression) -> Program {
        Program {
            main,
            parameters: Parameters::from(self.parameters),
            witness_types: WitnessTypes::from(self.witnesses),
            call_tracker: Arc::new(self.call_tracker),
        }
    }
}
