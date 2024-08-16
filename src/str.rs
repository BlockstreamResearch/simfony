//! Types for handling strings with invariants.

use std::sync::Arc;

/// Implementations for newtypes that wrap [`Arc<str>`].
macro_rules! wrapped_string {
    ($wrapper:ident) => {
        impl $wrapper {
            /// Access the inner string.
            pub fn as_inner(&self) -> &str {
                self.0.as_ref()
            }
        }

        impl std::fmt::Display for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }

        impl std::fmt::Debug for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

/// The name of a function.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionName(Arc<str>);

impl FunctionName {
    /// Create a function name.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid function name.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }

    /// Return the name of the main function.
    pub fn main() -> Self {
        Self(Arc::from("main"))
    }
}

wrapped_string!(FunctionName);

/// The identifier of a variable.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Identifier(Arc<str>);

impl Identifier {
    /// Create a variable identifier.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid variable identifier.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }
}

wrapped_string!(Identifier);

/// The name of a witness.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct WitnessName(Arc<str>);

impl WitnessName {
    /// Create a witness name.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid witness name.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }
}

wrapped_string!(WitnessName);

/// The name of a jet.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct JetName(Arc<str>);

impl JetName {
    /// Create a jet name.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid jet name.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }
}

wrapped_string!(JetName);

/// A string of decimal digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct UnsignedDecimal(Arc<str>);

impl UnsignedDecimal {
    /// Create a decimal string.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid decimal string.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }
}

wrapped_string!(UnsignedDecimal);
