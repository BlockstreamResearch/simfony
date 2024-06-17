use std::fmt;

use crate::error::Error;
use crate::num::U256;
use crate::parse::{Bits, Bytes, UnsignedDecimal};
use crate::types::UIntType;

/// Unsigned integer value.
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum UIntValue {
    /// 1-bit unsigned integer.
    U1(u8),
    /// 2-bit unsigned integer.
    U2(u8),
    /// 4-bit unsigned integer.
    U4(u8),
    /// 8-bit unsigned integer.
    U8(u8),
    /// 16-bit unsigned integer.
    U16(u16),
    /// 32-bit unsigned integer.
    U32(u32),
    /// 64-bit unsigned integer.
    U64(u64),
    /// 128-bit unsigned integer.
    U128(u128),
    /// 256-bit unsigned integer.
    U256(U256),
}

impl fmt::Display for UIntValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UIntValue::U1(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U2(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U4(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U8(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U16(n) => <u16 as fmt::Display>::fmt(n, f),
            UIntValue::U32(n) => <u32 as fmt::Display>::fmt(n, f),
            UIntValue::U64(n) => <u64 as fmt::Display>::fmt(n, f),
            UIntValue::U128(n) => <u128 as fmt::Display>::fmt(n, f),
            UIntValue::U256(n) => <U256 as fmt::Display>::fmt(n, f),
        }
    }
}

impl UIntValue {
    /// Get the type of type value.
    pub const fn get_type(self) -> UIntType {
        match self {
            UIntValue::U1(_) => UIntType::U1,
            UIntValue::U2(_) => UIntType::U2,
            UIntValue::U4(_) => UIntType::U4,
            UIntValue::U8(_) => UIntType::U8,
            UIntValue::U16(_) => UIntType::U16,
            UIntValue::U32(_) => UIntType::U32,
            UIntValue::U64(_) => UIntType::U64,
            UIntValue::U128(_) => UIntType::U128,
            UIntValue::U256(_) => UIntType::U256,
        }
    }

    /// Check if the value is of the given type.
    pub fn is_of_type(self, ty: UIntType) -> bool {
        self.get_type() == ty
    }

    /// Create a value of type [`u1`].
    ///
    /// ## Errors
    ///
    /// Value is greater than 1.
    pub const fn u1(value: u8) -> Result<Self, Error> {
        match value {
            0 | 1 => Ok(Self::U1(value)),
            _ => Err(Error::IntegerOutOfBounds(UIntType::U1)),
        }
    }

    /// Create a value of type [`u2`].
    ///
    /// ## Errors
    ///
    /// Value is greater than 3.
    pub const fn u2(value: u8) -> Result<Self, Error> {
        match value {
            0..=3 => Ok(Self::U2(value)),
            _ => Err(Error::IntegerOutOfBounds(UIntType::U2)),
        }
    }

    /// Create a value of type [`u4`].
    ///
    /// ## Errors
    ///
    /// Value is greater than 15.
    pub const fn u4(value: u8) -> Result<Self, Error> {
        match value {
            0..=15 => Ok(Self::U4(value)),
            _ => Err(Error::IntegerOutOfBounds(UIntType::U4)),
        }
    }

    /// Create an integer from a `decimal` string and type.
    pub fn parse_decimal(decimal: &UnsignedDecimal, ty: UIntType) -> Result<Self, Error> {
        let s = decimal.as_inner();
        match ty {
            UIntType::U1 => s.parse::<u8>().map_err(Error::from).and_then(Self::u1),
            UIntType::U2 => s.parse::<u8>().map_err(Error::from).and_then(Self::u2),
            UIntType::U4 => s.parse::<u8>().map_err(Error::from).and_then(Self::u4),
            UIntType::U8 => s.parse::<u8>().map_err(Error::from).map(Self::U8),
            UIntType::U16 => s.parse::<u16>().map_err(Error::from).map(Self::U16),
            UIntType::U32 => s.parse::<u32>().map_err(Error::from).map(Self::U32),
            UIntType::U64 => s.parse::<u64>().map_err(Error::from).map(Self::U64),
            UIntType::U128 => s.parse::<u128>().map_err(Error::from).map(Self::U128),
            UIntType::U256 => s.parse::<U256>().map_err(Error::from).map(Self::U256),
        }
    }
}

impl From<u8> for UIntValue {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}

impl From<u16> for UIntValue {
    fn from(value: u16) -> Self {
        Self::U16(value)
    }
}

impl From<u32> for UIntValue {
    fn from(value: u32) -> Self {
        Self::U32(value)
    }
}

impl From<u64> for UIntValue {
    fn from(value: u64) -> Self {
        Self::U64(value)
    }
}

impl From<u128> for UIntValue {
    fn from(value: u128) -> Self {
        Self::U128(value)
    }
}

impl From<U256> for UIntValue {
    fn from(value: U256) -> Self {
        Self::U256(value)
    }
}

impl TryFrom<&[u8]> for UIntValue {
    type Error = &'static str;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value.len() {
            1 => Ok(Self::U8(value[0])),
            2 => Ok(Self::U16(u16::from_be_bytes(value.try_into().unwrap()))),
            4 => Ok(Self::U32(u32::from_be_bytes(value.try_into().unwrap()))),
            8 => Ok(Self::U64(u64::from_be_bytes(value.try_into().unwrap()))),
            16 => Ok(Self::U128(u128::from_be_bytes(value.try_into().unwrap()))),
            32 => Ok(Self::U256(U256::from_byte_array(value.try_into().unwrap()))),
            _ => Err("Too many bytes"),
        }
    }
}

impl From<Bits> for UIntValue {
    fn from(value: Bits) -> Self {
        if let Some(byte) = value.as_u1() {
            Self::u1(byte).expect("Always <= 1")
        } else if let Some(byte) = value.as_u2() {
            Self::u2(byte).expect("Always <= 3")
        } else if let Some(byte) = value.as_u4() {
            Self::u4(byte).expect("Always <= 15")
        } else if let Some(bytes) = value.as_long() {
            Self::try_from(bytes).expect("At most 32 bytes")
        } else {
            unreachable!("Covered all bit string variants")
        }
    }
}

impl From<Bytes> for UIntValue {
    fn from(value: Bytes) -> Self {
        Self::try_from(value.as_ref()).expect("At most 32 bytes")
    }
}
