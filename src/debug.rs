use std::collections::HashMap;
use std::sync::Arc;

use simplicity::Cmr;

use crate::error::Span;
use crate::types::ResolvedType;
use crate::value::{StructuralValue, Value};

/// Tracker of Simfony call expressions inside Simplicity target code.
///
/// Tracking happens via CMRs that are inserted into the Simplicity target code.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DebugSymbols(HashMap<Cmr, TrackedCall>);

/// Call expression with a debug symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TrackedCall {
    text: Arc<str>,
    name: TrackedCallName,
}

/// Name of a call expression with a debug symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrackedCallName {
    Assert,
    Panic,
    Jet,
    UnwrapLeft(ResolvedType),
    UnwrapRight(ResolvedType),
    Unwrap,
}

/// Fallible call expression with runtime input value.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FallibleCall {
    text: Arc<str>,
    name: FallibleCallName,
}

/// Name of a fallible call expression with runtime input value.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum FallibleCallName {
    Assert,
    Panic,
    Jet,
    UnwrapLeft(Value),
    UnwrapRight(Value),
    Unwrap,
}

impl DebugSymbols {
    /// Insert a tracked call expression.
    /// Use the Simfony source `file` to extract the Simfony text of the expression.
    pub(crate) fn insert(&mut self, span: Span, name: TrackedCallName, file: &str) {
        let cmr = span.cmr();
        let text = remove_excess_whitespace(span.to_slice(file).unwrap_or(""));
        self.0.insert(
            cmr,
            TrackedCall {
                text: Arc::from(text),
                name,
            },
        );
    }

    /// Check if the given CMR tracks any call expressions.
    pub fn contains_key(&self, cmr: &Cmr) -> bool {
        self.0.contains_key(cmr)
    }

    /// Get the call expression that is tracked by the given CMR.
    pub fn get(&self, cmr: &Cmr) -> Option<&TrackedCall> {
        self.0.get(cmr)
    }
}

fn remove_excess_whitespace(s: &str) -> String {
    let mut last_was_space = true;
    let is_excess_whitespace = move |c: char| match c {
        ' ' => std::mem::replace(&mut last_was_space, true),
        '\n' => true,
        _ => {
            last_was_space = false;
            false
        }
    };
    s.replace(is_excess_whitespace, "")
}

impl TrackedCall {
    /// Access the text of the Simfony call expression.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Access the name of the call.
    pub fn name(&self) -> &TrackedCallName {
        &self.name
    }

    /// Supply the Simplicity input value of the call expression at runtime.
    ///
    /// Return `None` if the Simplicity input value is of the wrong type,
    /// according to the debug symbol.
    pub fn map_value(&self, value: &StructuralValue) -> Option<FallibleCall> {
        let name = match self.name() {
            TrackedCallName::Assert => FallibleCallName::Assert,
            TrackedCallName::Panic => FallibleCallName::Panic,
            TrackedCallName::Jet => FallibleCallName::Jet,
            TrackedCallName::UnwrapLeft(ty) => {
                Value::reconstruct(value, ty).map(FallibleCallName::UnwrapLeft)?
            }
            TrackedCallName::UnwrapRight(ty) => {
                Value::reconstruct(value, ty).map(FallibleCallName::UnwrapRight)?
            }
            TrackedCallName::Unwrap => FallibleCallName::Unwrap,
        };
        Some(FallibleCall {
            text: Arc::clone(&self.text),
            name,
        })
    }
}

impl FallibleCall {
    /// Access the Simfony text of the call expression.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Access the name of the call.
    pub fn name(&self) -> &FallibleCallName {
        &self.name
    }
}
