use miniscript::iter::{Tree, TreeLike};
use std::fmt;
use std::ops::Range;
use std::sync::Arc;

/// View of a slice as a balanced binary tree.
/// The slice must be nonempty.
///
/// Each node is labelled with a slice.
/// Leaves contain single elements.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BTreeSlice<'a, A>(&'a [A]);

impl<'a, A> BTreeSlice<'a, A> {
    /// View the slice as a balanced binary tree.
    ///
    /// ## Panics
    ///
    /// The slice is empty.
    pub fn from_slice(slice: &'a [A]) -> Self {
        assert!(!slice.is_empty(), "Slice must be nonempty");
        Self(slice)
    }
}

impl<'a, A: Clone> BTreeSlice<'a, A> {
    /// Fold the tree in post order, using the binary function `f`.
    pub fn fold<F>(self, f: F) -> A
    where
        F: Fn(A, A) -> A,
    {
        debug_assert!(!self.0.is_empty());

        let mut output = vec![];
        for item in self.post_order_iter() {
            match item.child_indices.len() {
                2 => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(f(l, r));
                }
                n => {
                    debug_assert!(n == 0);
                    debug_assert!(item.node.0.len() == 1);
                    output.push(item.node.0[0].clone());
                }
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

impl<'a, A: Clone> TreeLike for BTreeSlice<'a, A> {
    fn as_node(&self) -> Tree<Self> {
        match self.0.len() {
            0 => unreachable!("Empty slice"),
            1 => Tree::Nullary,
            n => {
                let next_pow2 = n.next_power_of_two();
                debug_assert!(0 < next_pow2 / 2);
                debug_assert!(0 < n - next_pow2 / 2);
                let half = next_pow2 / 2;
                let left = BTreeSlice::from_slice(&self.0[..half]);
                let right = BTreeSlice::from_slice(&self.0[half..]);
                Tree::Binary(left, right)
            }
        }
    }
}

/// Partition of a slice into blocks of (lengths of) powers of two.
///
/// The blocks start at (length) `N` and decrease to one in order.
/// Depending on the (length of the) slice, some blocks might be empty.
///
/// A partition forms a binary tree:
///
/// 1. A slice of length `l = 1` is a leaf
/// 2. A slice of length `l ≥ N` is a parent:
///     1. Left child: The block of the first `N` elements
///     2. Right child: The partition of the remaining `l - N` elements
/// 3. A slice of length `1 < l < N` is a parent:
///     1. Left child: The empty block
///     2. Right child: The partition of the remaining `l` elements
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Partition<'a, A> {
    Leaf(&'a [A]),
    Parent { slice: &'a [A], block_len: usize },
}

impl<'a, A> Partition<'a, A> {
    /// Partition the `slice` into blocks starting at the given `block_len`.
    ///
    /// ## Panics
    ///
    /// The `block_len` is not a power of two.
    ///
    /// The `block_len` is not large enough to partition the slice (2 * `block_len` ≤ slice length).
    pub fn from_slice(slice: &'a [A], block_len: usize) -> Self {
        assert!(
            block_len.is_power_of_two(),
            "The block length must be a power of two"
        );
        assert!(
            slice.len() < block_len * 2,
            "The block length must be large enough to partition the slice"
        );
        match block_len {
            1 => Self::Leaf(slice),
            _ => Self::Parent { slice, block_len },
        }
    }
}

impl<'a, A: Clone> Partition<'a, A> {
    /// Check if the partition is complete.
    ///
    /// A complete partition contains no empty blocks.
    pub fn is_complete(&self) -> bool {
        match self {
            Partition::Leaf(slice) => {
                debug_assert!(slice.len().is_power_of_two());
                slice.len() == 1
            }
            Partition::Parent { slice, block_len } => {
                debug_assert!(slice.len() < block_len * 2);
                slice.len() + 1 == block_len * 2
            }
        }
    }

    /// Fold the tree of blocks in post-order.
    ///
    /// There are two steps:
    /// 1. Function `f` converts each block (leaf node) into an output value.
    /// 2. Function `g` joins the outputs of each leaf in post-order.
    ///
    /// Function `f` must handle empty blocks if the partition is not complete.
    pub fn fold<B, F, G>(self, f: F, g: G) -> B
    where
        F: Fn(&[A]) -> B,
        G: Fn(B, B) -> B,
    {
        let mut output = vec![];
        for item in self.post_order_iter() {
            match item.node {
                Partition::Leaf(slice) => {
                    output.push(f(slice));
                }
                Partition::Parent { .. } => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(g(l, r));
                }
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

#[rustfmt::skip]
impl<'a, A: Clone> TreeLike for Partition<'a, A> {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Self::Leaf(..) => Tree::Nullary,
            Self::Parent { slice, block_len } => {
                debug_assert!(2 <= *block_len);
                let (l, r) = if slice.len() < *block_len {
                    (
                        Self::Leaf(&[]),
                        Self::from_slice(slice, block_len / 2),
                    )
                } else {
                    (
                        Self::Leaf(&slice[..*block_len]),
                        Self::from_slice(&slice[*block_len..], block_len / 2),
                    )
                };
                Tree::Binary(l, r)
            }
        }
    }
}

/// Convert a tree into a binary tree.
/// Each node has fanout at most two.
///
/// Nodes with at most two children (non-arrays) are preserved in the binary tree.
/// We call these nodes _normal nodes_.
///
/// Nodes with more than two children (arrays) are converted into balanced binary trees.
///
/// ## Example
///
/// Take a root node with children `a`, `b`, `c`.
///
/// ```text
///    .
///  / | \
/// a  b  c
/// ```
///
/// The 3-ary root is converted into two 2-ary nodes. The normal nodes `a`, `b`, `c` stay preserved.
///
/// ```text
///     .
///    / \
///   .   c
///  / \
/// a   b
/// ```
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct BinaryTree<T>(BinaryTreeInner<T>);

impl<T> BinaryTree<T> {
    /// Access the content of a normal node.
    pub fn as_normal(&self) -> Option<&T> {
        match &self.0 {
            BinaryTreeInner::Normal(tree) => Some(tree),
            _ => None,
        }
    }
}

impl<T: TreeLike> BinaryTree<T> {
    /// Convert a tree into a binary tree.
    ///
    /// ## Panics
    ///
    /// `<T as TreeLike>::as_node` returns `Tree::Nary` with an empty array.
    pub fn from_tree(tree: T) -> Self {
        Self(BinaryTreeInner::normal(tree))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum BinaryTreeInner<T> {
    /// Normal node (with at most two children).
    ///
    /// Must be constructed via [`BinaryTreeInner::normal()`].
    Normal(T),
    /// Array of at least two children.
    ///
    /// Must be constructed via [`BinaryTreeInner::array()`].
    Array(Arc<[T]>, Range<usize>),
}

impl<T: TreeLike> BinaryTreeInner<T> {
    /// Construct a binary tree from a tree.
    ///
    /// ## Panics
    ///
    /// `<T as TreeLike>::as_node` returns `Tree::Nary` with an empty array.
    // FIXME: Remove recursion
    fn normal(tree: T) -> Self {
        match tree.as_node() {
            Tree::Nary(array) => {
                let range = 0..array.len();
                Self::array(array, range)
            }
            _ => Self::Normal(tree),
        }
    }

    /// Construct a binary tree from an array.
    ///
    /// ## Panics
    ///
    /// Array is empty. Range is empty.
    ///
    /// `<T as TreeLike>::as_node` returns `Tree::Nary` with an empty array.
    // FIXME: Remove recursion
    fn array(array: Arc<[T]>, range: Range<usize>) -> Self {
        assert!(!array.is_empty(), "Arrays must be nonempty");
        match range.len() {
            0 => panic!("Range must be nonempty"),
            1 => Self::normal(array[range.start].clone()),
            _ => Self::Array(array, range),
        }
    }
}

impl<T: TreeLike> TreeLike for BinaryTree<T> {
    /// # Panics
    ///
    /// `<T as TreeLike>::as_node` returns `Tree::Nary` with an empty array.
    fn as_node(&self) -> Tree<Self> {
        match &self.0 {
            BinaryTreeInner::Normal(tree) => match tree.as_node() {
                Tree::Nullary => Tree::Nullary,
                Tree::Unary(l) => Tree::Unary(Self(BinaryTreeInner::normal(l))),
                Tree::Binary(l, r) => Tree::Binary(
                    Self(BinaryTreeInner::normal(l)),
                    Self(BinaryTreeInner::normal(r)),
                ),
                Tree::Nary(array) => {
                    let range = 0..array.len();
                    Self(BinaryTreeInner::array(array, range)).as_node()
                }
            },
            BinaryTreeInner::Array(array, range) => {
                debug_assert!(2 <= range.len());
                let n = range.len();
                let next_pow2 = n.next_power_of_two();
                let half = next_pow2 / 2;
                let left = Self(BinaryTreeInner::array(
                    Arc::clone(array),
                    range.start..range.start + half,
                ));
                let right = Self(BinaryTreeInner::array(
                    Arc::clone(array),
                    range.start + half..range.end,
                ));
                Tree::Binary(left, right)
            }
        }
    }
}

impl<T: TreeLike + fmt::Display> fmt::Display for BinaryTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            BinaryTreeInner::Normal(tree) => write!(f, "{tree}"),
            BinaryTreeInner::Array(..) => write!(f, "."),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::{Identifier, Pattern};
    use crate::scope::BasePattern;

    #[test]
    #[rustfmt::skip]
    fn fold_btree_slice() {
        let slice_output: [(&[&str], &str); 8] = [
            (&["a"], "a"),
            (&["a", "b"], "(ab)"),
            (&["a", "b", "c"], "((ab)c)"),
            (&["a", "b", "c", "d"], "((ab)(cd))"),
            (&["a", "b", "c", "d", "e"], "(((ab)(cd))e)"),
            (&["a", "b", "c", "d", "e", "f"], "(((ab)(cd))(ef))"),
            (&["a", "b", "c", "d", "e", "f", "g"], "(((ab)(cd))((ef)g))"),
            (&["a", "b", "c", "d", "e", "f", "g", "h"], "(((ab)(cd))((ef)(gh)))"),
        ];
        let concat = |a: String, b: String| format!("({a}{b})");

        for (slice, expected_output) in slice_output {
            let vector: Vec<_> = slice.iter().map(|s| s.to_string()).collect();
            let tree = BTreeSlice::from_slice(&vector);
            let output = tree.fold(concat);
            assert_eq!(&output, expected_output);
        }
    }

    #[test]
    #[rustfmt::skip]
    fn fold_partition() {
        let slice_len_output: [(&[&str], usize, &str); 14] = [
            (&[], 1, ""),
            (&["a"], 1, "a"),
            (&[], 2, "(:)"),
            (&["a"], 2, "(:a)"),
            (&["a", "b"], 2, "(ab:)"),
            (&["a", "b", "c"], 2, "(ab:c)"),
            (&[], 4, "(:(:))"),
            (&["a"], 4, "(:(:a))"),
            (&["a", "b"], 4, "(:(ab:))"),
            (&["a", "b", "c"], 4, "(:(ab:c))"),
            (&["a", "b", "c", "d"], 4, "(abcd:(:))"),
            (&["a", "b", "c", "d", "e"], 4, "(abcd:(:e))"),
            (&["a", "b", "c", "d", "e", "f"], 4, "(abcd:(ef:))"),
            (&["a", "b", "c", "d", "e", "f", "g"], 4, "(abcd:(ef:g))"),
        ];
        let process = |block: &[String]| block.join("");
        let join = |a: String, b: String| format!("({a}:{b})");

        for (slice, block_len, expected_output) in slice_len_output {
            let vector: Vec<_> = slice.iter().map(|s| s.to_string()).collect();
            let partition = Partition::from_slice(&vector, block_len);
            let output = partition.fold(process, join);
            assert_eq!(&output, expected_output);
        }
    }

    #[test]
    fn base_pattern() {
        let a = Pattern::Identifier(Identifier::from_str_unchecked("a"));
        let b = Pattern::Identifier(Identifier::from_str_unchecked("b"));
        let c = Pattern::Identifier(Identifier::from_str_unchecked("c"));
        let d = Pattern::Identifier(Identifier::from_str_unchecked("d"));
        let a_ = BasePattern::Identifier(Identifier::from_str_unchecked("a"));
        let b_ = BasePattern::Identifier(Identifier::from_str_unchecked("b"));
        let c_ = BasePattern::Identifier(Identifier::from_str_unchecked("c"));
        let d_ = BasePattern::Identifier(Identifier::from_str_unchecked("d"));

        let pattern_string = [
            // a = a
            (a.clone(), a_.clone()),
            // (a, b) = (a, b)
            (
                Pattern::product(a.clone(), b.clone()),
                BasePattern::product(a_.clone(), b_.clone()),
            ),
            // [a] = a
            (Pattern::array([a.clone()]).unwrap(), a_.clone()),
            // [[a]] = a
            (
                Pattern::array([Pattern::array([a.clone()]).unwrap()]).unwrap(),
                a_.clone(),
            ),
            // [a b] = (a, b)
            (
                Pattern::array([a.clone(), b.clone()]).unwrap(),
                BasePattern::product(a_.clone(), b_.clone()),
            ),
            // [a b c] = ((a, b), c)
            (
                Pattern::array([a.clone(), b.clone(), c.clone()]).unwrap(),
                BasePattern::product(BasePattern::product(a_.clone(), b_.clone()), c_.clone()),
            ),
            // [[a, b], [c, d]] = ((a, b), (c, d))
            (
                Pattern::array([
                    Pattern::array([a.clone(), b.clone()]).unwrap(),
                    Pattern::array([c.clone(), d.clone()]).unwrap(),
                ])
                .unwrap(),
                BasePattern::product(BasePattern::product(a_, b_), BasePattern::product(c_, d_)),
            ),
        ];

        for (pattern, expected_base_pattern) in pattern_string {
            let base_pattern = BasePattern::from(&pattern);
            assert_eq!(expected_base_pattern, base_pattern);
        }
    }
}
