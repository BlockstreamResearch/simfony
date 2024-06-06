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
pub enum Type {
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

impl<'a> TreeLike for &'a Type {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Type::Unit | Type::Boolean | Type::UInt(..) => Tree::Nullary,
            Type::Option(l) | Type::Array(l, _) | Type::List(l, _) => Tree::Unary(l),
            Type::Either(l, r) | Type::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

impl Type {
    /// Convert the type into a normalized unsigned integer type.
    /// Return the empty value if the conversion failed.
    pub fn to_uint(&self) -> Option<UIntType> {
        let mut integer_type = HashMap::<&Type, UIntType>::new();
        for data in self.post_order_iter() {
            match data.node {
                Type::Unit => {}
                Type::Either(l, r) => match (l.as_ref(), r.as_ref()) {
                    (Type::Unit, Type::Unit) => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                Type::Product(l, r) => {
                    let uint_l = integer_type.get(l.as_ref())?;
                    let uint_r = integer_type.get(r.as_ref())?;
                    if uint_l != uint_r {
                        return None;
                    }
                    let uint_ty = uint_l.double()?;
                    integer_type.insert(data.node, uint_ty);
                }
                Type::Option(r) => match r.as_ref() {
                    // Option<1> = u1
                    Type::Unit => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                Type::Boolean => {
                    integer_type.insert(data.node, UIntType::U1);
                }
                Type::UInt(ty) => {
                    integer_type.insert(data.node, *ty);
                }
                Type::Array(el, size) => {
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
                Type::List(el, bound) => match (el.as_ref(), *bound) {
                    // List<1, 2> = Option<1> = u1
                    (Type::Unit, NonZeroPow2Usize::TWO) => {
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
                Type::Unit => output.push(SimType::unit()),
                Type::Either(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::sum(l, r));
                }
                Type::Product(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::product(l, r));
                }
                Type::Option(_) => {
                    let r = output.pop().unwrap();
                    output.push(SimType::sum(SimType::unit(), r));
                }
                Type::Boolean => {
                    output.push(SimType::two_two_n(0));
                }
                Type::UInt(ty) => output.push(ty.to_simplicity()),
                Type::Array(_, size) => {
                    let el = output.pop().unwrap();
                    // Cheap clone because SimType consists of Arcs
                    let el_vector = vec![el; size.get()];
                    let tree = BTreeSlice::from_slice(&el_vector);
                    output.push(tree.fold(SimType::product));
                }
                Type::List(_, bound) => {
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Type::Unit => f.write_str("()")?,
                Type::Either(_, _) => match data.n_children_yielded {
                    0 => f.write_str("Either<")?,
                    1 => f.write_str(",")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(">")?;
                    }
                },
                Type::Product(_, _) => match data.n_children_yielded {
                    0 => f.write_str("(")?,
                    1 => f.write_str(", ")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(")")?;
                    }
                },
                Type::Option(_) => match data.n_children_yielded {
                    0 => f.write_str("Option<")?,
                    n => {
                        debug_assert!(n == 1);
                        f.write_str(">")?;
                    }
                },
                Type::Boolean => f.write_str("bool")?,
                Type::UInt(ty) => write!(f, "{ty}")?,
                Type::Array(_, size) => match data.n_children_yielded {
                    0 => f.write_str("[")?,
                    n => {
                        debug_assert!(n == 1);
                        write!(f, "; {size}]")?;
                    }
                },
                Type::List(_, bound) => match data.n_children_yielded {
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
