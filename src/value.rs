use std::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};

use crate::error::Error;
use crate::num::{NonZeroPow2Usize, U256};
use crate::parse::{Bits, Bytes, UnsignedDecimal};
use crate::types::{ResolvedType, TypeInner, UIntType};

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

/// Various value constructors.
pub trait ValueConstructible: Sized + From<Option<Self>> + From<bool> + From<UIntValue> {
    /// Create the unit value.
    fn unit() -> Self;

    /// Create the left value `Either::Left(inner)`.
    fn left(inner: Self) -> Self;

    /// Create the right value `Either::Right(inner)`.
    fn right(inner: Self) -> Self;

    /// Create the product value `(left, right)`.
    fn product(left: Self, right: Self) -> Self;

    /// Create an array from the given `elements`.
    ///
    /// ## Nonemptiness
    ///
    /// There must be at least one element.
    ///
    /// ## Errors
    ///
    /// Returns [`None`] if there are no elements.
    fn array<I: IntoIterator<Item = Self>>(elements: I) -> Option<Self>;

    /// Create `bound`ed list from the given `elements`.
    ///
    /// ## Boundedness
    ///
    /// There must be fewer `elements` than the given `bound`.
    /// The `bound` is an exclusive upper bound on the number of `elements`.
    ///
    /// ## Errors
    ///
    /// Returns [`None`] if there are too many elements.
    fn list<I: IntoIterator<Item = Self>>(elements: I, bound: NonZeroPow2Usize) -> Option<Self>;
}

/// Simfony value.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Value {
    /// Unit value.
    Unit,
    /// Left value.
    Left(Arc<Self>),
    /// Right value.
    Right(Arc<Self>),
    /// Product value.
    Product(Arc<Self>, Arc<Self>),
    /// Option value.
    Option(Option<Arc<Self>>),
    /// Boolean value.
    Boolean(bool),
    /// Unsigned integer.
    UInt(UIntValue),
    /// Nonempty array of values.
    // FIXME: Prevent construction of invalid arrays (that are empty)
    Array(Arc<[Self]>),
    /// Bounded list of values.
    // FIXME: Prevent construction of invalid lists (that run out of bounds)
    List(Arc<[Self]>, NonZeroPow2Usize),
}

impl<'a> TreeLike for &'a Value {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Value::Unit | Value::Option(None) | Value::Boolean(_) | Value::UInt(_) => Tree::Nullary,
            Value::Left(l) | Value::Right(l) | Value::Option(Some(l)) => Tree::Unary(l),
            Value::Product(l, r) => Tree::Binary(l, r),
            Value::Array(elements) | Value::List(elements, _) => {
                Tree::Nary(elements.iter().collect())
            }
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match &data.node {
                Value::Unit => f.write_str("()")?,
                Value::Left(_) => match data.n_children_yielded {
                    0 => f.write_str("Left(")?,
                    n => {
                        debug_assert_eq!(n, 1);
                        f.write_str(")")?;
                    }
                },
                Value::Right(_) => match data.n_children_yielded {
                    0 => f.write_str("Right(")?,
                    n => {
                        debug_assert_eq!(n, 1);
                        f.write_str(")")?;
                    }
                },
                Value::Product(_, _) => match data.n_children_yielded {
                    0 => f.write_str("(")?,
                    1 => f.write_str(", ")?,
                    n => {
                        debug_assert_eq!(n, 2);
                        f.write_str(")")?;
                    }
                },
                Value::Option(None) => f.write_str("None")?,
                Value::Option(Some(_)) => match data.n_children_yielded {
                    0 => f.write_str("Some(")?,
                    n => {
                        debug_assert_eq!(n, 1);
                        f.write_str(")")?;
                    }
                },
                Value::Boolean(bit) => write!(f, "{bit}")?,
                Value::UInt(integer) => write!(f, "{integer}")?,
                Value::Array(elements) => match data.n_children_yielded {
                    0 => f.write_str("[")?,
                    n if n == elements.len() => {
                        f.write_str("]")?;
                    }
                    n => {
                        debug_assert!(n < elements.len());
                        f.write_str(", ")?;
                    }
                },
                Value::List(elements, _) => match data.n_children_yielded {
                    0 => f.write_str("list![")?,
                    n if n == elements.len() => {
                        f.write_str("]")?;
                    }
                    n => {
                        debug_assert!(n < elements.len());
                        f.write_str(", ")?;
                    }
                },
            }
        }

        Ok(())
    }
}

impl ValueConstructible for Value {
    fn unit() -> Self {
        Self::Unit
    }

    fn left(inner: Self) -> Self {
        Self::Left(Arc::new(inner))
    }

    fn right(inner: Self) -> Self {
        Self::Right(Arc::new(inner))
    }

    fn product(left: Self, right: Self) -> Self {
        Self::Product(Arc::new(left), Arc::new(right))
    }

    fn array<I: IntoIterator<Item = Self>>(elements: I) -> Option<Self> {
        let elements: Arc<[Self]> = elements.into_iter().collect();
        match elements.is_empty() {
            false => Some(Self::Array(elements)),
            true => None,
        }
    }

    fn list<I: IntoIterator<Item = Self>>(elements: I, bound: NonZeroPow2Usize) -> Option<Self> {
        let elements: Arc<[Self]> = elements.into_iter().collect();
        match elements.len() < bound.get() {
            true => Some(Self::List(elements, bound)),
            false => None,
        }
    }
}

impl From<Option<Self>> for Value {
    fn from(value: Option<Self>) -> Self {
        Self::Option(value.map(Arc::new))
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Boolean(value)
    }
}

impl From<UIntValue> for Value {
    fn from(value: UIntValue) -> Self {
        Self::UInt(value)
    }
}

impl Value {
    /// Check if the value is of the given type.
    ///
    /// ## Errors
    ///
    /// A subvalue and the corresponding subtype didn't match.
    /// The method returns this mismatching value-type pair.
    pub fn is_of_type<'a>(
        &'a self,
        ty: &'a ResolvedType,
    ) -> Result<(), (&'a Value, &'a ResolvedType)> {
        let mut stack = vec![(self, ty)];
        while let Some((value, ty)) = stack.pop() {
            match (value, ty.as_inner()) {
                (Value::Unit, TypeInner::Unit)
                | (Value::Boolean(_), TypeInner::Boolean)
                | (Value::UInt(_), TypeInner::UInt(_))
                | (Value::Option(None), TypeInner::Option(_)) => {}
                (Value::Left(val_l), TypeInner::Either(ty_l, _))
                | (Value::Right(val_l), TypeInner::Either(_, ty_l))
                | (Value::Option(Some(val_l)), TypeInner::Option(ty_l)) => {
                    stack.push((val_l, ty_l))
                }
                (Value::Product(val_l, val_r), TypeInner::Product(ty_l, ty_r)) => {
                    stack.push((val_r, ty_r));
                    stack.push((val_l, ty_l));
                }
                (Value::Array(val_el), TypeInner::Array(ty_el, size))
                    if val_el.len() == size.get() =>
                {
                    stack.extend(val_el.iter().zip(std::iter::repeat(ty_el.as_ref())));
                }
                (Value::List(val_el, val_bound), TypeInner::List(ty_el, ty_bound))
                    if val_bound == ty_bound =>
                {
                    stack.extend(val_el.iter().zip(std::iter::repeat(ty_el.as_ref())));
                }
                _ => return Err((value, ty)),
            }
        }

        Ok(())
    }
}

/// Typed Simfony value.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TypedValue {
    value: Value,
    ty: ResolvedType,
}

impl TypedValue {
    /// Create a `value` of the given type.
    ///
    /// ## Errors
    ///
    /// The `value` is not of the given type.
    pub fn new(value: Value, ty: ResolvedType) -> Result<Self, Error> {
        match value.is_of_type(&ty) {
            Ok(()) => Ok(Self { value, ty }),
            // TODO: Include local value-type mismatch in Error::TypeValueMismatch
            Err(..) => Err(Error::TypeValueMismatch(ty)),
        }
    }

    /// Access the Simfony value.
    pub const fn value(&self) -> &Value {
        &self.value
    }

    /// Access the Simfony type.
    pub const fn ty(&self) -> &ResolvedType {
        &self.ty
    }
}

impl From<TypedValue> for Value {
    fn from(value: TypedValue) -> Self {
        value.value
    }
}

impl From<TypedValue> for ResolvedType {
    fn from(value: TypedValue) -> Self {
        value.ty
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{StructuralType, TypeConstructible};

    #[test]
    fn display_value() {
        let array = Value::array([Value::unit(), Value::unit(), Value::unit()]).unwrap();
        assert_eq!("[(), (), ()]", &array.to_string());
        let list = Value::list([Value::unit()], NonZeroPow2Usize::TWO).unwrap();
        assert_eq!("list![()]", &list.to_string());
    }

    #[test]
    fn value_is_of_type() {
        let bit = Value::from(false);
        let actual_boolean = ResolvedType::boolean();
        let structural_boolean = ResolvedType::either(ResolvedType::unit(), ResolvedType::unit());
        assert_eq!(
            StructuralType::from(&actual_boolean),
            StructuralType::from(&structural_boolean)
        );
        assert!(bit.is_of_type(&actual_boolean).is_ok());
        assert!(bit.is_of_type(&structural_boolean).is_err());
    }
}
