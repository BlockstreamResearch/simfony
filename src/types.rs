use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::types::{CompleteBound, Final};

use crate::array::{BTreeSlice, Partition};
use crate::num::NonZeroPow2Usize;
use crate::parse::Identifier;

/// Primitives of the Simfony type system, excluding type aliases.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[non_exhaustive]
pub enum TypeInner<A> {
    /// Sum of the left and right types
    Either(A, A),
    /// Option of the inner type
    Option(A),
    /// Boolean type
    Boolean,
    /// Unsigned integer type
    UInt(UIntType),
    /// Tuple of potentially different types
    Tuple(Arc<[A]>),
    /// Array of the same type
    Array(A, NonZeroUsize),
    /// List of the same type
    List(A, NonZeroPow2Usize),
}

impl<A> TypeInner<A> {
    /// Helper method for displaying type primitives based on the number of yielded children.
    ///
    /// We cannot implement [`fmt::Display`] because `n_children_yielded` is an extra argument.
    fn display(&self, f: &mut fmt::Formatter<'_>, n_children_yielded: usize) -> fmt::Result {
        match self {
            TypeInner::Either(_, _) => match n_children_yielded {
                0 => f.write_str("Either<"),
                1 => f.write_str(","),
                n => {
                    debug_assert_eq!(n, 2);
                    f.write_str(">")
                }
            },
            TypeInner::Option(_) => match n_children_yielded {
                0 => f.write_str("Option<"),
                n => {
                    debug_assert_eq!(n, 1);
                    f.write_str(">")
                }
            },
            TypeInner::Boolean => f.write_str("bool"),
            TypeInner::UInt(ty) => write!(f, "{ty}"),
            TypeInner::Tuple(elements) => match n_children_yielded {
                0 => {
                    f.write_str("(")?;
                    if 0 == elements.len() {
                        f.write_str(")")?;
                    }
                    Ok(())
                }
                n if n == elements.len() => {
                    if n == 1 {
                        f.write_str(",")?;
                    }
                    f.write_str(")")
                }
                n => {
                    debug_assert!(n < elements.len());
                    f.write_str(", ")
                }
            },
            TypeInner::Array(_, size) => match n_children_yielded {
                0 => f.write_str("["),
                n => {
                    debug_assert_eq!(n, 1);
                    write!(f, "; {size}]")
                }
            },
            TypeInner::List(_, bound) => match n_children_yielded {
                0 => f.write_str("List<"),
                n => {
                    debug_assert_eq!(n, 1);
                    write!(f, ", {bound}>")
                }
            },
        }
    }
}

/// Unsigned integer type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum UIntType {
    /// 1-bit unsigned integer
    U1,
    /// 2-bit unsigned integer
    U2,
    /// 4-bit unsigned integer
    U4,
    /// 8-bit unsigned integer
    U8,
    /// 16-bit unsigned integer
    U16,
    /// 32-bit unsigned integer
    U32,
    /// 64-bit unsigned integer
    U64,
    /// 128-bit unsigned integer
    U128,
    /// 256-bit unsigned integer
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
        let mut current = value.as_ref();
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
pub trait TypeConstructible: Sized + From<UIntType> {
    /// Create a sum of the given `left` and `right` types.
    fn either(left: Self, right: Self) -> Self;

    /// Create an option of the given `inner` type.
    fn option(inner: Self) -> Self;

    /// Create the Boolean type.
    fn boolean() -> Self;

    /// Create a tuple from the given `elements`.
    ///
    /// The empty tuple is the unit type.
    /// A tuple of two types is a product.
    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self;

    /// Create the unit type.
    fn unit() -> Self {
        Self::tuple([])
    }

    /// Create a product of the given `left` and `right` types.
    fn product(left: Self, right: Self) -> Self {
        Self::tuple([left, right])
    }

    /// Create an array with `size` many values of the `element` type.
    fn array(element: Self, size: NonZeroUsize) -> Self;

    /// Create a list with less than `bound` many values of the `element` type.
    fn list(element: Self, bound: NonZeroPow2Usize) -> Self;
}

/// Simfony type without type aliases.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ResolvedType(TypeInner<Arc<Self>>);

impl ResolvedType {
    /// Access the inner type primitive.
    pub fn as_inner(&self) -> &TypeInner<Arc<Self>> {
        &self.0
    }
}

impl TypeConstructible for ResolvedType {
    fn either(left: Self, right: Self) -> Self {
        Self(TypeInner::Either(Arc::new(left), Arc::new(right)))
    }

    fn option(inner: Self) -> Self {
        Self(TypeInner::Option(Arc::new(inner)))
    }

    fn boolean() -> Self {
        Self(TypeInner::Boolean)
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self(TypeInner::Tuple(
            elements.into_iter().map(Arc::new).collect(),
        ))
    }

    fn array(element: Self, size: NonZeroUsize) -> Self {
        Self(TypeInner::Array(Arc::new(element), size))
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        Self(TypeInner::List(Arc::new(element), bound))
    }
}

impl<'a> TreeLike for &'a ResolvedType {
    fn as_node(&self) -> Tree<Self> {
        match &self.0 {
            TypeInner::Boolean | TypeInner::UInt(..) => Tree::Nullary,
            TypeInner::Option(l) | TypeInner::Array(l, _) | TypeInner::List(l, _) => Tree::Unary(l),
            TypeInner::Either(l, r) => Tree::Binary(l, r),
            TypeInner::Tuple(elements) => Tree::Nary(elements.iter().map(Arc::as_ref).collect()),
        }
    }
}

impl fmt::Display for ResolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            data.node.0.display(f, data.n_children_yielded)?;
        }
        Ok(())
    }
}

impl From<UIntType> for ResolvedType {
    fn from(value: UIntType) -> Self {
        Self(TypeInner::UInt(value))
    }
}

/// Simfony type with type aliases.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct AliasedType(AliasedInner);

/// Type alias or primitive.
///
/// Private struct to allow future changes.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum AliasedInner {
    /// Type alias
    Alias(Identifier),
    /// Type primitive
    Inner(TypeInner<Arc<AliasedType>>),
}

impl AliasedType {
    /// Create a type alias from the given `identifier`.
    pub fn alias(identifier: Identifier) -> Self {
        Self(AliasedInner::Alias(identifier))
    }

    /// Resolve all aliases in the type based on the given map of `aliases` to types.
    pub fn resolve<F>(&self, mut get_alias: F) -> Result<ResolvedType, Identifier>
    where
        F: FnMut(&Identifier) -> Option<ResolvedType>,
    {
        let mut output = vec![];
        for data in self.post_order_iter() {
            match &data.node.0 {
                AliasedInner::Alias(alias) => {
                    let resolved = get_alias(alias).ok_or(alias.clone())?;
                    output.push(resolved);
                }
                AliasedInner::Inner(inner) => match inner {
                    TypeInner::Either(_, _) => {
                        let right = output.pop().unwrap();
                        let left = output.pop().unwrap();
                        output.push(ResolvedType::either(left, right));
                    }
                    TypeInner::Option(_) => {
                        let inner = output.pop().unwrap();
                        output.push(ResolvedType::option(inner));
                    }
                    TypeInner::Boolean => output.push(ResolvedType::boolean()),
                    TypeInner::UInt(integer) => output.push(ResolvedType::from(*integer)),
                    TypeInner::Tuple(_) => {
                        let size = data.node.n_children();
                        let elements = output.split_off(output.len() - size);
                        debug_assert_eq!(elements.len(), size);
                        output.push(ResolvedType::tuple(elements));
                    }
                    TypeInner::Array(_, size) => {
                        let element = output.pop().unwrap();
                        output.push(ResolvedType::array(element, *size));
                    }
                    TypeInner::List(_, bound) => {
                        let element = output.pop().unwrap();
                        output.push(ResolvedType::list(element, *bound));
                    }
                },
            }
        }
        debug_assert_eq!(output.len(), 1);
        Ok(output.pop().unwrap())
    }
}

impl TypeConstructible for AliasedType {
    fn either(left: Self, right: Self) -> Self {
        Self(AliasedInner::Inner(TypeInner::Either(
            Arc::new(left),
            Arc::new(right),
        )))
    }

    fn option(inner: Self) -> Self {
        Self(AliasedInner::Inner(TypeInner::Option(Arc::new(inner))))
    }

    fn boolean() -> Self {
        Self(AliasedInner::Inner(TypeInner::Boolean))
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self(AliasedInner::Inner(TypeInner::Tuple(
            elements.into_iter().map(Arc::new).collect(),
        )))
    }

    fn array(element: Self, size: NonZeroUsize) -> Self {
        Self(AliasedInner::Inner(TypeInner::Array(
            Arc::new(element),
            size,
        )))
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        Self(AliasedInner::Inner(TypeInner::List(
            Arc::new(element),
            bound,
        )))
    }
}

impl<'a> TreeLike for &'a AliasedType {
    fn as_node(&self) -> Tree<Self> {
        match &self.0 {
            AliasedInner::Alias(_) => Tree::Nullary,
            AliasedInner::Inner(inner) => match inner {
                TypeInner::Boolean | TypeInner::UInt(..) => Tree::Nullary,
                TypeInner::Option(l) | TypeInner::Array(l, _) | TypeInner::List(l, _) => {
                    Tree::Unary(l)
                }
                TypeInner::Either(l, r) => Tree::Binary(l, r),
                TypeInner::Tuple(elements) => {
                    Tree::Nary(elements.iter().map(Arc::as_ref).collect())
                }
            },
        }
    }
}

impl fmt::Display for AliasedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match &data.node.0 {
                AliasedInner::Alias(alias) => write!(f, "{alias}")?,
                AliasedInner::Inner(inner) => inner.display(f, data.n_children_yielded)?,
            }
        }
        Ok(())
    }
}

impl From<UIntType> for AliasedType {
    fn from(value: UIntType) -> Self {
        Self(AliasedInner::Inner(TypeInner::UInt(value)))
    }
}

/// Internal structure of a Simfony type.
/// 1:1 isomorphism to Simplicity.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct StructuralType(Arc<Final>);

impl AsRef<Final> for StructuralType {
    fn as_ref(&self) -> &Final {
        &self.0
    }
}

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
            match &data.node.0 {
                TypeInner::Either(_, _) => {
                    let right = output.pop().unwrap();
                    let left = output.pop().unwrap();
                    output.push(StructuralType::either(left, right));
                }
                TypeInner::Option(_) => {
                    let inner = output.pop().unwrap();
                    output.push(StructuralType::option(inner));
                }
                TypeInner::Boolean => output.push(StructuralType::boolean()),
                TypeInner::UInt(integer) => output.push(StructuralType::from(*integer)),
                TypeInner::Tuple(_) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(StructuralType::tuple(elements));
                }
                TypeInner::Array(_, size) => {
                    let element = output.pop().unwrap();
                    output.push(StructuralType::array(element, *size));
                }
                TypeInner::List(_, bound) => {
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
    fn either(left: Self, right: Self) -> Self {
        Self(Final::sum(left.0, right.0))
    }

    fn option(inner: Self) -> Self {
        Self::either(Self::unit(), inner)
    }

    fn boolean() -> Self {
        Self::either(Self::unit(), Self::unit())
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        let elements: Vec<_> = elements.into_iter().collect();
        match elements.is_empty() {
            true => Self::unit(),
            false => {
                let tree = BTreeSlice::from_slice(&elements);
                tree.fold(Self::product)
            }
        }
    }

    // Keep this implementation to prevent an infinite loop in <Self as TypeConstructible>::tuple
    fn unit() -> Self {
        Self(Final::unit())
    }

    // Keep this implementation to prevent an infinite loop in <Self as TypeConstructible>::tuple
    fn product(left: Self, right: Self) -> Self {
        Self(Final::product(left.0, right.0))
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
    /// Convert into an unfinalized type that can be used in Simplicity's unification algorithm.
    pub fn to_unfinalized(&self) -> simplicity::types::Type {
        simplicity::types::Type::from(self.0.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_type() {
        let unit = ResolvedType::unit();
        assert_eq!("()", &unit.to_string());
        let singleton = ResolvedType::tuple([ResolvedType::from(UIntType::U1)]);
        assert_eq!("(u1,)", &singleton.to_string());
        let pair = ResolvedType::tuple([
            ResolvedType::from(UIntType::U1),
            ResolvedType::from(UIntType::U8),
        ]);
        assert_eq!("(u1, u8)", &pair.to_string());
        let triple = ResolvedType::tuple([
            ResolvedType::from(UIntType::U1),
            ResolvedType::from(UIntType::U8),
            ResolvedType::from(UIntType::U16),
        ]);
        assert_eq!("(u1, u8, u16)", &triple.to_string());
        let array = ResolvedType::array(ResolvedType::unit(), NonZeroUsize::new(3).unwrap());
        assert_eq!("[(); 3]", &array.to_string());
        let list = ResolvedType::list(ResolvedType::unit(), NonZeroPow2Usize::TWO);
        assert_eq!("List<(), 2>", &list.to_string());
    }
}
