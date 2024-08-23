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

/// Implementation of [`arbitrary::Arbitrary`] for wrapped string types,
/// such that strings of 1 to 10 letters `a` to `z` are generated.
///
/// The space of lowercase letter strings includes values that are invalid
/// according to the grammar of the particular string type. For instance,
/// keywords are reserved. However, this should not affect fuzzing.
macro_rules! impl_arbitrary_lowercase_alpha {
    ($wrapper:ident) => {
        #[cfg(feature = "arbitrary")]
        impl<'a> arbitrary::Arbitrary<'a> for $wrapper {
            fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
                let len = u.int_in_range(1..=10)?;
                let mut string = String::with_capacity(len);
                for _ in 0..len {
                    let offset = u.int_in_range(0..=25)?;
                    string.push((b'a' + offset) as char)
                }
                Ok(Self::from_str_unchecked(string.as_str()))
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
impl_arbitrary_lowercase_alpha!(FunctionName);

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
impl_arbitrary_lowercase_alpha!(Identifier);

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
impl_arbitrary_lowercase_alpha!(WitnessName);

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

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for JetName {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        u.choose(&simplicity::jet::Elements::ALL)
            .map(simplicity::jet::Elements::to_string)
            .map(Arc::from)
            .map(Self)
    }
}

/// A string of decimal digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Decimal(Arc<str>);

impl Decimal {
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

wrapped_string!(Decimal);

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Decimal {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=9)?;
            string.push((b'0' + offset) as char)
        }
        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// A string of binary digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Binary(Arc<str>);

impl Binary {
    /// Create a binary string.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid binary string.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }
}

wrapped_string!(Binary);

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Binary {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=1)?;
            let bin_digit = (b'0' + offset) as char;
            string.push(bin_digit);
        }
        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// A string of hexadecimal digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Hexadecimal(Arc<str>);

impl Hexadecimal {
    /// Create a hexadecimal string.
    ///
    /// ## Precondition
    ///
    /// The string must be a valid hexadecimal string.
    ///
    /// ## Panics
    ///
    /// Panics may occur down the line if the precondition is not satisfied.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }
}

wrapped_string!(Hexadecimal);

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Hexadecimal {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=15)?;
            let hex_digit = match offset {
                0..=9 => (b'0' + offset) as char,
                10..=15 => (b'a' + (offset - 10)) as char,
                _ => unreachable!(),
            };
            string.push(hex_digit);
        }
        Ok(Self::from_str_unchecked(string.as_str()))
    }
}
