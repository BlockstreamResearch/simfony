use crate::num::NonZeroPow2Usize;
use miniscript::iter::{Tree, TreeLike};

/// View of a slice as a balanced binary tree.
///
/// Each node is labelled with a slice.
/// Leaves contain single elements.
///
/// The tree is right-associative:
/// `&[a b c]` becomes `&[a] (&[b] &[c])`.
///
/// The tree is empty if the slice is empty.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BTreeSlice<'a, A>(&'a [A]);

impl<'a, A> BTreeSlice<'a, A> {
    /// View the slice as a balanced binary tree.
    pub fn from_slice(slice: &'a [A]) -> Self {
        Self(slice)
    }
}

impl<'a, A: Clone> BTreeSlice<'a, A> {
    /// Fold the tree in post order, using the binary function `f`.
    ///
    /// Returns `None` if the tree is empty.
    pub fn fold<F>(self, f: F) -> Option<A>
    where
        F: Fn(A, A) -> A,
    {
        if self.0.is_empty() {
            return None;
        }

        let mut output = vec![];
        for item in self.post_order_iter() {
            match item.child_indices.len() {
                2 => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(f(l, r));
                }
                n => {
                    debug_assert_eq!(n, 0);
                    debug_assert_eq!(item.node.0.len(), 1);
                    output.push(item.node.0[0].clone());
                }
            }
        }

        debug_assert_eq!(output.len(), 1);
        output.pop()
    }
}

impl<'a, A: Clone> TreeLike for BTreeSlice<'a, A> {
    fn as_node(&self) -> Tree<Self> {
        match self.0.len() {
            0 | 1 => Tree::Nullary,
            n => {
                let next_pow2 = n.next_power_of_two();
                debug_assert!(0 < next_pow2 / 2);
                debug_assert!(0 < n - next_pow2 / 2);
                let half = n - next_pow2 / 2;
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
    Leaf {
        slice: &'a [A],
        size: usize,
    },
    Parent {
        slice: &'a [A],
        bound: NonZeroPow2Usize,
    },
}

impl<'a, A> Partition<'a, A> {
    /// Partition a `slice` of less than `bound` many elements into blocks.
    ///
    /// ## Panics
    ///
    /// The `slice` has `bound` many elements or more.
    pub fn from_slice(slice: &'a [A], bound: NonZeroPow2Usize) -> Self {
        assert!(
            slice.len() < bound.get(),
            "The slice must be shorter than the given bound"
        );
        match bound {
            NonZeroPow2Usize::TWO => Self::Leaf { slice, size: 1 },
            _ => Self::Parent { slice, bound },
        }
    }
}

impl<'a, A: Clone> Partition<'a, A> {
    /// Check if the partition is complete.
    ///
    /// A complete partition contains no empty blocks.
    pub fn is_complete(&self) -> bool {
        match self {
            Partition::Leaf { slice, size } => slice.len() == *size,
            Partition::Parent { slice, bound } => slice.len() + 1 == bound.get(),
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
        F: Fn(&[A], usize) -> B,
        G: Fn(B, B) -> B,
    {
        let mut output = vec![];
        for item in self.post_order_iter() {
            match item.node {
                Partition::Leaf { slice, size } => {
                    output.push(f(slice, size));
                }
                Partition::Parent { .. } => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(g(l, r));
                }
            }
        }

        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

#[rustfmt::skip]
impl<'a, A: Clone> TreeLike for Partition<'a, A> {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Self::Leaf {..} => Tree::Nullary,
            Self::Parent { slice, bound } => {
                debug_assert!(NonZeroPow2Usize::TWO < *bound);
                let smaller_bound = bound.checked_div2().unwrap();

                let (l, r) = if slice.len() < smaller_bound.get() {
                    (
                        Self::Leaf { slice: &[], size: smaller_bound.get() },
                        Self::from_slice(slice, smaller_bound),
                    )
                } else {
                    (
                        Self::Leaf { slice: &slice[..smaller_bound.get()], size: smaller_bound.get() },
                        Self::from_slice(&slice[smaller_bound.get()..], smaller_bound),
                    )
                };
                Tree::Binary(l, r)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pattern::{BasePattern, Pattern};
    use crate::str::Identifier;

    #[test]
    #[rustfmt::skip]
    fn fold_btree_slice() {
        let slice_output: [(&[&str], &str); 9] = [
            (&[], ""),
            (&["a"], "a"),
            (&["a", "b"], "(ab)"),
            (&["a", "b", "c"], "(a(bc))"),
            (&["a", "b", "c", "d"], "((ab)(cd))"),
            (&["a", "b", "c", "d", "e"], "(a((bc)(de)))"),
            (&["a", "b", "c", "d", "e", "f"], "((ab)((cd)(ef)))"),
            (&["a", "b", "c", "d", "e", "f", "g"], "((a(bc))((de)(fg)))"),
            (&["a", "b", "c", "d", "e", "f", "g", "h"], "(((ab)(cd))((ef)(gh)))"),
        ];
        let concat = |a: String, b: String| format!("({a}{b})");

        for (slice, expected_output) in slice_output {
            let vector: Vec<_> = slice.iter().map(|s| s.to_string()).collect();
            let tree = BTreeSlice::from_slice(&vector);
            let output = tree.fold(concat).unwrap_or_default();
            assert_eq!(&output, expected_output);
        }
    }

    #[test]
    #[rustfmt::skip]
    fn fold_partition() {
        let slice_len_output: [(&[&str], usize, &str); 14] = [
            (&[], 2, ""),
            (&["a"], 2, "a"),
            (&[], 4, "(:)"),
            (&["a"], 4, "(:a)"),
            (&["a", "b"], 4, "(ab:)"),
            (&["a", "b", "c"], 4, "(ab:c)"),
            (&[], 8, "(:(:))"),
            (&["a"], 8, "(:(:a))"),
            (&["a", "b"], 8, "(:(ab:))"),
            (&["a", "b", "c"], 8, "(:(ab:c))"),
            (&["a", "b", "c", "d"], 8, "(abcd:(:))"),
            (&["a", "b", "c", "d", "e"], 8, "(abcd:(:e))"),
            (&["a", "b", "c", "d", "e", "f"], 8, "(abcd:(ef:))"),
            (&["a", "b", "c", "d", "e", "f", "g"], 8, "(abcd:(ef:g))"),
        ];
        let process = |block: &[String], _| block.join("");
        let join = |a: String, b: String| format!("({a}:{b})");

        for (slice, bound, expected_output) in slice_len_output {
            let vector: Vec<_> = slice.iter().map(|s| s.to_string()).collect();
            let partition = Partition::from_slice(&vector, NonZeroPow2Usize::new_unchecked(bound));
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
            (Pattern::array([a.clone()]), a_.clone()),
            // [[a]] = a
            (Pattern::array([Pattern::array([a.clone()])]), a_.clone()),
            // [a b] = (a, b)
            (
                Pattern::array([a.clone(), b.clone()]),
                BasePattern::product(a_.clone(), b_.clone()),
            ),
            // [a b c] = (a, (b, c))
            (
                Pattern::array([a.clone(), b.clone(), c.clone()]),
                BasePattern::product(a_.clone(), BasePattern::product(b_.clone(), c_.clone())),
            ),
            // [[a, b], [c, d]] = ((a, b), (c, d))
            (
                Pattern::array([
                    Pattern::array([a.clone(), b.clone()]),
                    Pattern::array([c.clone(), d.clone()]),
                ]),
                BasePattern::product(BasePattern::product(a_, b_), BasePattern::product(c_, d_)),
            ),
        ];

        for (pattern, expected_base_pattern) in pattern_string {
            let base_pattern = BasePattern::from(&pattern);
            assert_eq!(expected_base_pattern, base_pattern);
        }
    }
}
