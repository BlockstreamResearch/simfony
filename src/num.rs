/// Implementation for newtypes that wrap a number `u8`, `u16`, ...
/// such that the number has some property.
/// The newtype needs to have a constructor `Self::new(inner) -> Option<Self>`.
macro_rules! checked_num {
    (
        $wrapper: ident,
        $inner: ty,
        $description: expr
    ) => {
        impl $wrapper {
            /// Access the value as a primitive type.
            pub const fn get(&self) -> usize {
                self.0
            }
        }

        impl std::fmt::Display for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::fmt::Debug for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(self, f)
            }
        }

        impl std::str::FromStr for $wrapper {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                let n = s.parse::<$inner>().map_err(|e| e.to_string())?;
                Self::new(n).ok_or(format!("{s} is not {}", $description))
            }
        }
    };
}

/// An integer that is known to be a power of two with nonzero exponent.
///
/// The integer is equal to 2^n for some n > 0.
///
/// The integer is strictly greater than 1.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct NonZeroPow2Usize(usize);

impl NonZeroPow2Usize {
    /// Smallest power of two with nonzero exponent.
    // FIXME `std::option::Option::<T>::unwrap` is not yet stable as a const fn
    // pub const TWO: Self = Self::new(2).unwrap();
    pub const TWO: Self = Self(2);

    /// Create a power of two with nonzero exponent.
    pub const fn new(n: usize) -> Option<Self> {
        if n.is_power_of_two() && 1 < n {
            Some(Self(n))
        } else {
            None
        }
    }

    /// Create the smallest power of two with nonzero exponent greater equal `n`.
    pub const fn next(n: usize) -> Self {
        if n < 2 {
            Self::TWO
        } else {
            // FIXME `std::option::Option::<T>::unwrap` is not yet stable as a const fn
            // Self::new(n.next_power_of_two()).unwrap()
            Self(n.next_power_of_two())
        }
    }

    /// Return the binary logarithm of the value.
    ///
    /// The integer is equal to 2^n. Return n.
    pub const fn log2(self) -> u32 {
        self.0.trailing_zeros()
    }
}

checked_num!(NonZeroPow2Usize, usize, "a power of two greater than 1");
