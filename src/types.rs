use std::collections::HashMap;
use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::types::Type as SimType;

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
    /// Double the bit width of the type.
    /// Return the empty value upon overflow.
    pub fn double(&self) -> Option<Self> {
        match self {
            UIntType::U1 => Some(UIntType::U2),
            UIntType::U2 => Some(UIntType::U4),
            UIntType::U4 => Some(UIntType::U8),
            UIntType::U8 => Some(UIntType::U16),
            UIntType::U16 => Some(UIntType::U32),
            UIntType::U32 => Some(UIntType::U64),
            UIntType::U64 => Some(UIntType::U128),
            UIntType::U128 => Some(UIntType::U256),
            UIntType::U256 => None,
        }
    }

    /// Convert the type into a Simplicity type.
    pub fn to_simplicity(self) -> SimType {
        match self {
            UIntType::U1 => SimType::two_two_n(0),
            UIntType::U2 => SimType::two_two_n(1),
            UIntType::U4 => SimType::two_two_n(2),
            UIntType::U8 => SimType::two_two_n(3),
            UIntType::U16 => SimType::two_two_n(4),
            UIntType::U32 => SimType::two_two_n(5),
            UIntType::U64 => SimType::two_two_n(6),
            UIntType::U128 => SimType::two_two_n(7),
            UIntType::U256 => SimType::two_two_n(8),
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

impl ResolvedType {
    /// Convert the type into a normalized unsigned integer type.
    /// Return the empty value if the conversion failed.
    pub fn to_uint(&self) -> Option<UIntType> {
        let mut integer_type = HashMap::<&ResolvedType, UIntType>::new();
        for data in self.post_order_iter() {
            match data.node {
                ResolvedType::Unit => {}
                ResolvedType::Either(l, r) => match (l.as_ref(), r.as_ref()) {
                    (ResolvedType::Unit, ResolvedType::Unit) => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                ResolvedType::Product(l, r) => {
                    let uint_l = integer_type.get(l.as_ref())?;
                    let uint_r = integer_type.get(r.as_ref())?;
                    if uint_l != uint_r {
                        return None;
                    }
                    let uint_ty = uint_l.double()?;
                    integer_type.insert(data.node, uint_ty);
                }
                ResolvedType::Option(r) => match r.as_ref() {
                    // Option<1> = u1
                    ResolvedType::Unit => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                ResolvedType::Boolean => {
                    integer_type.insert(data.node, UIntType::U1);
                }
                ResolvedType::UInt(ty) => {
                    integer_type.insert(data.node, *ty);
                }
                ResolvedType::Array(el, size) => {
                    if !size.is_power_of_two() {
                        return None;
                    }

                    let mut uint = *integer_type.get(el.as_ref())?;
                    for _ in 0..size.trailing_zeros() {
                        match uint.double() {
                            Some(doubled_uint) => uint = doubled_uint,
                            None => return None,
                        }
                    }
                    integer_type.insert(data.node, uint);
                }
                ResolvedType::List(el, bound) => match (el.as_ref(), *bound) {
                    // List<1, 2> = Option<1> = u1
                    (ResolvedType::Unit, NonZeroPow2Usize::TWO) => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
            }
        }

        integer_type.remove(self)
    }

    /// Convert the type into a Simplicity type.
    pub fn to_simplicity(&self) -> SimType {
        let mut output = vec![];

        for data in self.post_order_iter() {
            match data.node {
                ResolvedType::Unit => output.push(SimType::unit()),
                ResolvedType::Either(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::sum(l, r));
                }
                ResolvedType::Product(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::product(l, r));
                }
                ResolvedType::Option(_) => {
                    let r = output.pop().unwrap();
                    output.push(SimType::sum(SimType::unit(), r));
                }
                ResolvedType::Boolean => {
                    output.push(SimType::two_two_n(0));
                }
                ResolvedType::UInt(ty) => output.push(ty.to_simplicity()),
                ResolvedType::Array(_, size) => {
                    let el = output.pop().unwrap();
                    // Cheap clone because SimType consists of Arcs
                    let el_vector = vec![el; size.get()];
                    let tree = BTreeSlice::from_slice(&el_vector);
                    output.push(tree.fold(SimType::product));
                }
                ResolvedType::List(_, bound) => {
                    let el = output.pop().unwrap();
                    // Cheap clone because SimType consists of Arcs
                    let el_vector = vec![el; bound.get() - 1];
                    let partition = Partition::from_slice(&el_vector, bound.get() / 2);
                    debug_assert!(partition.is_complete());
                    let process = |block: &[SimType]| -> SimType {
                        debug_assert!(!block.is_empty());
                        let tree = BTreeSlice::from_slice(block);
                        let array = tree.fold(SimType::product);
                        SimType::sum(SimType::unit(), array)
                    };
                    output.push(partition.fold(process, SimType::product));
                }
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
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
