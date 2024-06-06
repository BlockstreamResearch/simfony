use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::types::{CompleteBound, Final};

use crate::array::{BTreeSlice, Partition};
use crate::num::NonZeroPow2Usize;

/// A Simphony type.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[non_exhaustive]
pub enum ResolvedType {
    Unit,
    Either(Arc<Self>, Arc<Self>),
    Product(Arc<Self>, Arc<Self>),
    Option(Arc<Self>),
    Boolean,
    UInt(UIntType),
    Array(Arc<Self>, NonZeroUsize),
    List(Arc<Self>, NonZeroPow2Usize),
}

/// Normalized unsigned integer type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum UIntType {
    U1,
    U2,
    U4,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256,
}

impl UIntType {
    /// Take `n` and return the `2^n`-bit unsigned integer type.
    pub fn two_n(n: u32) -> Option<Self> {
        match n {
            0 => Some(UIntType::U1),
            1 => Some(UIntType::U2),
            2 => Some(UIntType::U4),
            3 => Some(UIntType::U8),
            4 => Some(UIntType::U16),
            5 => Some(UIntType::U32),
            6 => Some(UIntType::U64),
            7 => Some(UIntType::U128),
            8 => Some(UIntType::U256),
            _ => None,
        }
    }
}

impl fmt::Display for UIntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UIntType::U1 => f.write_str("u1"),
            UIntType::U2 => f.write_str("u2"),
            UIntType::U4 => f.write_str("u4"),
            UIntType::U8 => f.write_str("u8"),
            UIntType::U16 => f.write_str("u16"),
            UIntType::U32 => f.write_str("u32"),
            UIntType::U64 => f.write_str("u64"),
            UIntType::U128 => f.write_str("u128"),
            UIntType::U256 => f.write_str("u256"),
        }
    }
}

impl<'a> TryFrom<&'a StructuralType> for UIntType {
    type Error = ();

    fn try_from(value: &StructuralType) -> Result<Self, Self::Error> {
        let mut current = value.as_inner();
        let mut n = 0;
        while let Some((left, right)) = current.as_product() {
            if left.tmr() != right.tmr() {
                return Err(());
            }
            current = left;
            n += 1;
        }
        if let Some((left, right)) = current.as_sum() {
            if left.is_unit() && right.is_unit() {
                return UIntType::two_n(n).ok_or(());
            }
        }
        Err(())
    }
}

impl<'a> TryFrom<&'a ResolvedType> for UIntType {
    type Error = ();

    fn try_from(value: &ResolvedType) -> Result<Self, Self::Error> {
        UIntType::try_from(&StructuralType::from(value))
    }
}

/// Various type constructors.
pub trait TypeConstructible: Sized {
    /// Create the unit type.
    fn unit() -> Self;

    /// Create a sum of the given `left` and `right` types.
    fn either(left: Self, right: Self) -> Self;

    /// Create a product of the given `left` and `right` types.
    fn product(left: Self, right: Self) -> Self;

    /// Create an option of the given `inner` type.
    fn option(inner: Self) -> Self;

    /// Create the Boolean type.
    fn boolean() -> Self;

    /// Create an unsigned `integer` type.
    fn uint(integer: UIntType) -> Self;

    /// Create an array with `size` many values of the `element` type.
    fn array(element: Self, size: NonZeroUsize) -> Self;

    /// Create a list with less than `bound` many values of the `element` type.
    fn list(element: Self, bound: NonZeroPow2Usize) -> Self;
}

impl TypeConstructible for ResolvedType {
    fn unit() -> Self {
        Self::Unit
    }

    fn either(left: Self, right: Self) -> Self {
        Self::Either(Arc::new(left), Arc::new(right))
    }

    fn product(left: Self, right: Self) -> Self {
        Self::Product(Arc::new(left), Arc::new(right))
    }

    fn option(inner: Self) -> Self {
        Self::Option(Arc::new(inner))
    }

    fn boolean() -> Self {
        Self::Boolean
    }

    fn uint(integer: UIntType) -> Self {
        Self::UInt(integer)
    }

    fn array(element: Self, size: NonZeroUsize) -> Self {
        Self::Array(Arc::new(element), size)
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        Self::List(Arc::new(element), bound)
    }
}

impl<'a> TreeLike for &'a ResolvedType {
    fn as_node(&self) -> Tree<Self> {
        match self {
            ResolvedType::Unit | ResolvedType::Boolean | ResolvedType::UInt(..) => Tree::Nullary,
            ResolvedType::Option(l) | ResolvedType::Array(l, _) | ResolvedType::List(l, _) => {
                Tree::Unary(l)
            }
            ResolvedType::Either(l, r) | ResolvedType::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

impl fmt::Display for ResolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                ResolvedType::Unit => f.write_str("()")?,
                ResolvedType::Either(_, _) => match data.n_children_yielded {
                    0 => f.write_str("Either<")?,
                    1 => f.write_str(",")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(">")?;
                    }
                },
                ResolvedType::Product(_, _) => match data.n_children_yielded {
                    0 => f.write_str("(")?,
                    1 => f.write_str(", ")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(")")?;
                    }
                },
                ResolvedType::Option(_) => match data.n_children_yielded {
                    0 => f.write_str("Option<")?,
                    n => {
                        debug_assert!(n == 1);
                        f.write_str(">")?;
                    }
                },
                ResolvedType::Boolean => f.write_str("bool")?,
                ResolvedType::UInt(ty) => write!(f, "{ty}")?,
                ResolvedType::Array(_, size) => match data.n_children_yielded {
                    0 => f.write_str("[")?,
                    n => {
                        debug_assert!(n == 1);
                        write!(f, "; {size}]")?;
                    }
                },
                ResolvedType::List(_, bound) => match data.n_children_yielded {
                    0 => f.write_str("List<")?,
                    n => {
                        debug_assert!(n == 1);
                        write!(f, ", {bound}>")?;
                    }
                },
            }
        }

        Ok(())
    }
}

/// Internal structure of a Simfony type.
/// 1:1 isomorphism to Simplicity.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct StructuralType(Arc<Final>);

impl TreeLike for StructuralType {
    fn as_node(&self) -> Tree<Self> {
        match self.0.bound() {
            CompleteBound::Unit => Tree::Nullary,
            CompleteBound::Sum(l, r) | CompleteBound::Product(l, r) => {
                Tree::Binary(Self(l.clone()), Self(r.clone()))
            }
        }
    }
}

impl From<UIntType> for StructuralType {
    fn from(value: UIntType) -> Self {
        let inner = match value {
            UIntType::U1 => Final::two_two_n(0),
            UIntType::U2 => Final::two_two_n(1),
            UIntType::U4 => Final::two_two_n(2),
            UIntType::U8 => Final::two_two_n(3),
            UIntType::U16 => Final::two_two_n(4),
            UIntType::U32 => Final::two_two_n(5),
            UIntType::U64 => Final::two_two_n(6),
            UIntType::U128 => Final::two_two_n(7),
            UIntType::U256 => Final::two_two_n(8),
        };
        Self(inner)
    }
}

impl<'a> From<&'a ResolvedType> for StructuralType {
    fn from(value: &ResolvedType) -> Self {
        let mut output = vec![];
        for data in value.post_order_iter() {
            match &data.node {
                ResolvedType::Unit => output.push(StructuralType::unit()),
                ResolvedType::Either(_, _) => {
                    let right = output.pop().unwrap();
                    let left = output.pop().unwrap();
                    output.push(StructuralType::either(left, right));
                }
                ResolvedType::Product(_, _) => {
                    let right = output.pop().unwrap();
                    let left = output.pop().unwrap();
                    output.push(StructuralType::product(left, right));
                }
                ResolvedType::Option(_) => {
                    let inner = output.pop().unwrap();
                    output.push(StructuralType::option(inner));
                }
                ResolvedType::Boolean => output.push(StructuralType::boolean()),
                ResolvedType::UInt(integer) => output.push(StructuralType::uint(*integer)),
                ResolvedType::Array(_, size) => {
                    let element = output.pop().unwrap();
                    output.push(StructuralType::array(element, *size));
                }
                ResolvedType::List(_, bound) => {
                    let element = output.pop().unwrap();
                    output.push(StructuralType::list(element, *bound));
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

impl TypeConstructible for StructuralType {
    fn unit() -> Self {
        Self(Final::unit())
    }

    fn either(left: Self, right: Self) -> Self {
        Self(Final::sum(left.0, right.0))
    }

    fn product(left: Self, right: Self) -> Self {
        Self(Final::product(left.0, right.0))
    }

    fn option(inner: Self) -> Self {
        Self::either(Self::unit(), inner)
    }

    fn boolean() -> Self {
        Self::either(Self::unit(), Self::unit())
    }

    fn uint(integer: UIntType) -> Self {
        Self::from(integer)
    }

    fn array(element: Self, size: NonZeroUsize) -> Self {
        // Cheap clone because Arc<Final> consists of Arcs
        let el_vector = vec![element.0; size.get()];
        let tree = BTreeSlice::from_slice(&el_vector);
        let inner = tree.fold(Final::product);
        Self(inner)
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        // Cheap clone because Arc<Final> consists of Arcs
        let el_vector = vec![element.0; bound.get() - 1];
        let partition = Partition::from_slice(&el_vector, bound.get() / 2);
        debug_assert!(partition.is_complete());
        let process = |block: &[Arc<Final>]| -> Arc<Final> {
            debug_assert!(!block.is_empty());
            let tree = BTreeSlice::from_slice(block);
            let array = tree.fold(Final::product);
            Final::sum(Final::unit(), array)
        };
        let inner = partition.fold(process, Final::product);
        Self(inner)
    }
}

impl StructuralType {
    /// Access the finalized Simplicity type.
    pub fn as_inner(&self) -> &Final {
        self.0.as_ref()
    }

    /// Convert into an unfinalized type that can be used in Simplicity's unification algorithm.
    pub fn to_unfinalized(&self) -> simplicity::types::Type {
        simplicity::types::Type::from(self.0.clone())
    }
}
