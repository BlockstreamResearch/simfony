use std::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::Value as SimValue;

use crate::array::{BTreeSlice, Partition};
use crate::error::Error;
use crate::num::{NonZeroPow2Usize, U256};
use crate::parse::{Bits, Bytes, UnsignedDecimal};
use crate::types::{ResolvedType, StructuralType, TypeInner, UIntType};

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

impl<'a> From<&'a Bits> for UIntValue {
    fn from(value: &Bits) -> Self {
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

impl<'a> From<&'a Bytes> for UIntValue {
    fn from(value: &Bytes) -> Self {
        Self::try_from(value.as_ref()).expect("At most 32 bytes")
    }
}

/// Various value constructors.
pub trait ValueConstructible: Sized + From<Option<Self>> + From<bool> + From<UIntValue> {
    /// Create the left value `Either::Left(inner)`.
    fn left(inner: Self) -> Self;

    /// Create the right value `Either::Right(inner)`.
    fn right(inner: Self) -> Self;

    /// Create a tuple from the given `elements`.
    ///
    /// The empty tuple is the unit value.
    /// A tuple of two values is a product.
    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self;

    /// Create the unit value.
    fn unit() -> Self {
        Self::tuple([])
    }

    /// Create the product value `(left, right)`.
    fn product(left: Self, right: Self) -> Self {
        Self::tuple([left, right])
    }

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
    /// Left value.
    Left(Arc<Self>),
    /// Right value.
    Right(Arc<Self>),
    /// Option value.
    Option(Option<Arc<Self>>),
    /// Boolean value.
    Boolean(bool),
    /// Unsigned integer.
    UInt(UIntValue),
    /// Tuple of values.
    ///
    /// Each component may have a different type.
    Tuple(Arc<[Self]>),
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
            Value::Option(None) | Value::Boolean(_) | Value::UInt(_) => Tree::Nullary,
            Value::Left(l) | Value::Right(l) | Value::Option(Some(l)) => Tree::Unary(l),
            Value::Tuple(elements) | Value::Array(elements) | Value::List(elements, _) => {
                Tree::Nary(elements.iter().collect())
            }
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match &data.node {
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
                Value::Tuple(elements) => match data.n_children_yielded {
                    0 => {
                        f.write_str("(")?;
                        if 0 == elements.len() {
                            f.write_str(")")?;
                        }
                    }
                    n if n == elements.len() => {
                        if n == 1 {
                            f.write_str(",")?;
                        }
                        f.write_str(")")?;
                    }
                    n => {
                        debug_assert!(n < elements.len());
                        f.write_str(", ")?;
                    }
                },
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
    fn left(inner: Self) -> Self {
        Self::Left(Arc::new(inner))
    }

    fn right(inner: Self) -> Self {
        Self::Right(Arc::new(inner))
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self::Tuple(elements.into_iter().collect())
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
                (Value::Boolean(_), TypeInner::Boolean)
                | (Value::UInt(_), TypeInner::UInt(_))
                | (Value::Option(None), TypeInner::Option(_)) => {}
                (Value::Left(val_l), TypeInner::Either(ty_l, _))
                | (Value::Right(val_l), TypeInner::Either(_, ty_l))
                | (Value::Option(Some(val_l)), TypeInner::Option(ty_l)) => {
                    stack.push((val_l, ty_l))
                }
                (Value::Tuple(val_el), TypeInner::Tuple(ty_el)) if val_el.len() == ty_el.len() => {
                    stack.extend(val_el.iter().zip(ty_el.iter().map(Arc::as_ref)));
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

/// Structure of a Simfony value.
/// 1:1 isomorphism to Simplicity.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct StructuralValue(Arc<SimValue>);

impl AsRef<SimValue> for StructuralValue {
    fn as_ref(&self) -> &SimValue {
        &self.0
    }
}

impl From<StructuralValue> for Arc<SimValue> {
    fn from(value: StructuralValue) -> Self {
        value.0
    }
}

impl TreeLike for StructuralValue {
    fn as_node(&self) -> Tree<Self> {
        match self.as_ref() {
            SimValue::Unit => Tree::Nullary,
            SimValue::SumL(l) | SimValue::SumR(l) => Tree::Unary(Self(l.clone())),
            SimValue::Prod(l, r) => Tree::Binary(Self(l.clone()), Self(r.clone())),
        }
    }
}

impl ValueConstructible for StructuralValue {
    fn left(inner: Self) -> Self {
        Self(SimValue::sum_l(inner.0))
    }

    fn right(inner: Self) -> Self {
        Self(SimValue::sum_r(inner.0))
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        let elements: Vec<Self> = elements.into_iter().collect();
        match elements.is_empty() {
            true => Self::unit(),
            false => {
                let tree = BTreeSlice::from_slice(&elements);
                tree.fold(Self::product)
            }
        }
    }

    // Keep this implementation to prevent an infinite loop in <Self as ValueConstructible>::tuple
    fn unit() -> Self {
        Self(SimValue::unit())
    }

    // Keep this implementation to prevent an infinite loop in <Self as ValueConstructible>::tuple
    fn product(left: Self, right: Self) -> Self {
        Self(SimValue::prod(left.0, right.0))
    }

    fn array<I: IntoIterator<Item = Self>>(elements: I) -> Option<Self> {
        let elements: Vec<Self> = elements.into_iter().collect();
        if elements.is_empty() {
            return None;
        }
        let tree = BTreeSlice::from_slice(&elements);
        Some(tree.fold(Self::product))
    }

    fn list<I: IntoIterator<Item = Self>>(elements: I, bound: NonZeroPow2Usize) -> Option<Self> {
        let elements: Vec<Self> = elements.into_iter().collect();
        if bound.get() <= elements.len() {
            return None;
        }
        let partition = Partition::from_slice(&elements, bound.get() / 2);
        let process = |block: &[Self]| -> Self {
            if block.is_empty() {
                return Self::from(None);
            }
            let tree = BTreeSlice::from_slice(block);
            let array = tree.fold(Self::product);
            Self::from(Some(array))
        };
        Some(partition.fold(process, Self::product))
    }
}

impl From<Option<Self>> for StructuralValue {
    fn from(value: Option<Self>) -> Self {
        match value {
            None => Self::left(Self::unit()),
            Some(inner) => Self::right(inner),
        }
    }
}

impl From<bool> for StructuralValue {
    fn from(value: bool) -> Self {
        match value {
            false => Self::left(Self::unit()),
            true => Self::right(Self::unit()),
        }
    }
}

impl From<UIntValue> for StructuralValue {
    fn from(value: UIntValue) -> Self {
        match value {
            UIntValue::U1(n) => Self(SimValue::u1(n)),
            UIntValue::U2(n) => Self(SimValue::u2(n)),
            UIntValue::U4(n) => Self(SimValue::u4(n)),
            UIntValue::U8(n) => Self(SimValue::u8(n)),
            UIntValue::U16(n) => Self(SimValue::u16(n)),
            UIntValue::U32(n) => Self(SimValue::u32(n)),
            UIntValue::U64(n) => Self(SimValue::u64(n)),
            UIntValue::U128(n) => Self(SimValue::u128(n)),
            UIntValue::U256(n) => Self(SimValue::u256_from_slice(n.as_ref())),
        }
    }
}

impl<'a> From<&'a Value> for StructuralValue {
    fn from(value: &Value) -> Self {
        let mut output = vec![];
        for data in value.post_order_iter() {
            match &data.node {
                Value::Left(_) => {
                    let inner = output.pop().unwrap();
                    output.push(Self::left(inner));
                }
                Value::Right(_) => {
                    let inner = output.pop().unwrap();
                    output.push(Self::right(inner));
                }
                Value::Option(None) => output.push(Self::from(None)),
                Value::Option(Some(_)) => {
                    let inner = output.pop().unwrap();
                    output.push(Self::from(Some(inner)));
                }
                Value::Boolean(bit) => output.push(Self::from(*bit)),
                Value::UInt(integer) => output.push(Self::from(*integer)),
                Value::Tuple(_) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::tuple(elements));
                }
                Value::Array(_) => {
                    let size = data.node.n_children();
                    debug_assert!(0 < size);
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::array(elements).unwrap());
                }
                Value::List(_, bound) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert!(elements.len() < bound.get());
                    output.push(Self::list(elements, *bound).unwrap());
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

impl StructuralValue {
    /// Check if the value is of the given type.
    pub fn is_of_type(&self, ty: &StructuralType) -> bool {
        self.as_ref().is_of_type(ty.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{StructuralType, TypeConstructible};

    #[test]
    fn display_value() {
        let unit = Value::unit();
        assert_eq!("()", &unit.to_string());
        let singleton = Value::tuple([Value::from(UIntValue::U1(1))]);
        assert_eq!("(1,)", &singleton.to_string());
        let pair = Value::tuple([
            Value::from(UIntValue::U1(1)),
            Value::from(UIntValue::U8(42)),
        ]);
        assert_eq!("(1, 42)", &pair.to_string());
        let triple = Value::tuple([
            Value::from(UIntValue::U1(1)),
            Value::from(UIntValue::U8(42)),
            Value::from(UIntValue::U16(1337)),
        ]);
        assert_eq!("(1, 42, 1337)", &triple.to_string());
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
