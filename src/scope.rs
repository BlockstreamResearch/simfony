use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};

use crate::array::{DirectedTree, Direction};
use crate::parse::{Function, FunctionName, Identifier, Pattern};
use crate::{named::ProgExt, ProgNode};

/// Tracker of variable bindings.
///
/// Each Simfony expression expects an _input value_.
/// A Simfony expression is translated into a Simplicity expression
/// that similarly expects an _input value_.
/// Simfony variable names are translated into Simplicity expressions
/// that extract the seeked value from the input value of the encompassing expression.
///
/// Each (nested) block expression introduces a new scope.
/// Bindings from inner scopes overwrite bindings from outer scopes.
/// Bindings live as long as their scope.
#[derive(Debug, Clone)]
pub struct GlobalScope {
    /// For each scope, the set of assigned variables.
    ///
    /// A stack of scopes. Each scope is a stack of patterns.
    /// New patterns are pushed onto the top _(current, innermost)_ scope.
    ///
    /// The stack of scopes corresponds to a _pattern tree_.
    ///
    /// The stack `[[p1], [p2, p3]]` corresponds to a nested product of patterns:
    ///
    /// ```text
    ///    .
    ///   / \
    /// p3   .
    ///     / \
    ///   p2   p1
    /// ```
    ///
    /// And so on.
    ///
    /// Inner scopes occur higher in the tree than outer scopes.
    /// Later assignments occur higher in the tree than earlier assignments.
    ///
    /// The pattern tree is isomorphic to the _current input value_.
    /// The isomorphism maps variable names from the pattern tree to values from the input.
    ///
    /// ```text
    ///    .              .
    ///   / \            / \
    /// p3   .         v3   .
    ///     / \            / \
    ///   p2   p1   ↔    v2   v1
    ///
    /// p3 ↔ v3
    /// p2 ↔ v2
    /// p1 ↔ v1
    /// ```
    variables: Vec<Vec<Pattern>>,
    /// For each scope, the set of declared functions.
    functions: Vec<Vec<Function>>,
}

impl Default for GlobalScope {
    fn default() -> Self {
        Self::new(Pattern::Ignore)
    }
}

impl GlobalScope {
    /// Create a new [`GlobalScope`] for an `input` of the given shape.
    pub fn new(input: Pattern) -> Self {
        Self {
            variables: vec![vec![input]],
            functions: vec![vec![]],
        }
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(vec![]);
        self.functions.push(vec![]);
    }

    /// Pop a scope from the stack.
    ///
    /// # Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Empty stack");
        self.functions.pop().expect("Empty stack");
    }

    /// Push an assignment to the current scope.
    ///
    /// The input was updated in a let statement `let p = v`:
    ///
    /// ```text
    ///   .
    ///  / \
    /// v   previous
    /// ```
    ///
    /// Update the pattern tree accordingly:
    ///
    /// ```text
    ///   .
    ///  / \
    /// p   previous
    /// ```
    pub fn insert(&mut self, pattern: Pattern) {
        self.variables.last_mut().unwrap().push(pattern);
    }

    /// Return a pattern that corresponds to the current input value.
    fn to_pattern(&self) -> Pattern {
        let mut it = self.variables.iter().flat_map(|scope| scope.iter());
        let first = it.next().unwrap();
        it.cloned()
            .fold(first.clone(), |acc, next| Pattern::product(next, acc))
    }

    /// Get a Simplicity expression that returns a value of the shape of the target.
    /// The expression consumes the current input value.
    ///
    /// ## Example
    ///
    /// ```text
    /// let a: u8 = 0;
    /// let b = {
    ///     let b: u8 = 1;
    ///     let c: u8 = 2;
    ///     (a, b)  // here we seek the value of `(a, b)`
    /// };
    /// ```
    ///
    /// The pattern tree (left) and the input value (right) are as follows:
    ///
    /// ```text
    ///    .            .
    ///   / \          / \
    ///  c   .        2   .
    ///     / \          / \
    ///    b   .   ↔    1   .
    ///       / \          / \
    ///      a   _        0  ()
    /// ```
    ///
    /// The expression `drop pair (drop take iden) (take iden)` returns the seeked value.
    ///
    /// ## Panics
    ///
    /// A variable is undefined.
    pub fn get(&self, target: &Pattern) -> ProgNode {
        let env_pattern = self.to_pattern();
        match env_pattern.translate(target) {
            Ok(expr) => expr,
            Err(identifier) => panic!("\"{identifier}\" is undefined"),
        }
    }

    /// Declare a function in the current scope.
    pub fn insert_function(&mut self, function: Function) {
        self.functions.last_mut().unwrap().push(function);
    }

    /// Get the function from the current scope.
    ///
    /// ## Panics
    ///
    /// Function is undeclared.
    pub fn get_function(&self, name: &FunctionName) -> &Function {
        match self
            .functions
            .iter()
            .rev() // innermost scope has precedence
            .flat_map(|scope| scope.iter().rev()) // last declaration has precedence
            .find(|function| function.name() == name)
        {
            Some(function) => function,
            None => panic!("Function \"{name}\" is undeclared"),
        }
    }
}

impl Pattern {
    /// Access the identifier inside the pattern.
    pub fn get_identifier(&self) -> Option<&Identifier> {
        match self {
            Pattern::Identifier(i) => Some(i),
            _ => None,
        }
    }

    /// Get a sequence of take-drop-iden that returns the value of the given variable.
    /// The sequence takes a Simplicity value of the shape of this pattern as input.
    fn get_path(&self, identifier: &Identifier) -> Option<Vec<Short>> {
        let base_pattern = self.to_base();
        let directed_tree = DirectedTree::from(&base_pattern);
        let equals_identifier = |pattern: &Pattern| {
            pattern
                .get_identifier()
                .map(|i| i == identifier)
                .unwrap_or(false)
        };
        let path = directed_tree.find(equals_identifier)?.1;
        let short = path
            .into_iter()
            .filter_map(|d| match d {
                Direction::Left => Some(Short::O),
                Direction::Right => Some(Short::I),
                _ => None,
            })
            .collect();
        Some(short)
    }

    /// Get a Simplicity expression that returns a value of the shape of the target.
    /// The expression takes a Simplicity value of the shape of this pattern as input.
    fn get_translation_node(&self, target: &Self) -> Result<TranslationNode, Identifier> {
        let mut output = vec![];
        for data in target.to_base().post_order_iter() {
            match data.node {
                Pattern::Identifier(i) => {
                    let path = self.get_path(i).ok_or(i.clone())?;
                    output.push(TranslationNode::Short(path));
                }
                Pattern::Ignore => {
                    output.push(TranslationNode::Unit);
                }
                Pattern::Product(..) => {
                    let node_r = output.pop().unwrap();
                    let node_l = output.pop().unwrap();
                    output.push(TranslationNode::Pair(Arc::new(node_l), Arc::new(node_r)));
                }
                Pattern::Array(_) => unreachable!(),
            }
        }
        debug_assert!(output.len() == 1);
        Ok(output.pop().unwrap())
    }

    /// Get a compressed Simplicity expression that returns a value of the shape of the target.
    /// The expression takes a Simplicity value of the shape of this pattern as input.
    pub fn translate(&self, other: &Self) -> Result<ProgNode, Identifier> {
        let node = self.get_translation_node(other)?;
        let compressed = Arc::new(node.compress());
        Ok(compressed.to_expr())
    }
}

/// Abbreviation for the take or drop combinator.
///
/// Sequences of [`Short::O`] and [`Short::I`] are followed by an implicit `iden` combinator.
/// Because `iden` always follows, it doesn't make sense to explicitly add it in code.
/// The sequence `[Short::O, Short::I]` stands for `take drop iden`, and so on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Short {
    /// Take
    O,
    /// Drop
    I,
}

/// Simplicity expression that translates a nested Simplicity product value into another.
///
/// Only a small set of combinators is needed for this operation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TranslationNode {
    Unit,
    Short(Vec<Short>),
    Pair(Arc<Self>, Arc<Self>),
}

impl<'a> TreeLike for &'a TranslationNode {
    fn as_node(&self) -> Tree<Self> {
        match self {
            TranslationNode::Unit | TranslationNode::Short(_) => Tree::Nullary,
            TranslationNode::Pair(l, r) => Tree::Binary(l, r),
        }
    }
}

impl TranslationNode {
    /// Eliminate an unnecessary pair if possible.
    /// Return the minimized node.
    fn eliminate_pair(&self) -> Option<Self> {
        if let Self::Pair(l, r) = self {
            match (l.as_ref(), r.as_ref()) {
                // xoh ▵ unit ↦ xh, where x ∈ {o, i}*
                (Self::Short(vec), Self::Unit) => {
                    let (last, prefix) = vec.split_last()?;
                    if let Short::O = last {
                        return Some(Self::Short(prefix.to_vec()));
                    }
                }
                // unit ▵ xih ↦ xh, where x ∈ {o, i}*
                (Self::Unit, Self::Short(vec)) => {
                    let (last, prefix) = vec.split_last()?;
                    if let Short::I = last {
                        return Some(Self::Short(prefix.to_vec()));
                    }
                }
                // xoh ▵ xih ↦ xh, where x ∈ {o, i}*
                (Self::Short(vec_l), Self::Short(vec_r)) => {
                    let (last_l, prefix_l) = vec_l.split_last()?;
                    let (last_r, prefix_r) = vec_r.split_last()?;
                    if let (Short::O, Short::I) = (last_l, last_r) {
                        if prefix_l == prefix_r {
                            return Some(Self::Short(prefix_l.to_vec()));
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Recursively eliminate all unnecessary pairs.
    /// Return the minimized node.
    fn compress(&self) -> Self {
        let mut output = vec![];
        for data in self.post_order_iter() {
            match data.node {
                Self::Unit | Self::Short(..) => {
                    output.push(data.node.clone());
                }
                Self::Pair(..) => {
                    let compressed_r = output.pop().unwrap();
                    let compressed_l = output.pop().unwrap();
                    let pair = Self::Pair(Arc::new(compressed_l), Arc::new(compressed_r));

                    if let Some(compressed_pair) = pair.eliminate_pair() {
                        output.push(compressed_pair);
                    } else {
                        output.push(pair);
                    }
                }
            }
        }
        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }

    /// Eliminate an unnecessary take / drop if possible.
    /// Return the left and right child of the minimized node, and the parent combinator.
    ///
    /// [`TranslationNode`] doesn't support take / drop combinators with arbitrary children,
    /// so the minimized node is returned in parts. This function is called when [`TranslationNode`]
    /// is converted into [`ProgNode`]. The latter supports arbitrary take / drop combinators.
    fn eliminate_take_drop(&self) -> Option<(Self, Self, Short)> {
        if let Self::Pair(l, r) = self {
            // ox ▵ oy ↦ o(x ▵ y), where x, y ∈ {o, i}*
            // ix ▵ iy ↦ i(x ▵ y), where x, y ∈ {o, i}*
            if let (Self::Short(vec_l), Self::Short(vec_r)) = (l.as_ref(), r.as_ref()) {
                let (first_l, suffix_l) = vec_l.split_first()?;
                let (first_r, suffix_r) = vec_r.split_first()?;
                if first_l == first_r {
                    return Some((
                        Self::Short(suffix_l.to_vec()),
                        Self::Short(suffix_r.to_vec()),
                        *first_l,
                    ));
                }
            }
        }
        None
    }

    /// Convert a [`TranslateNode`] into the corresponding Simplicity expression.
    fn to_expr(self: Arc<Self>) -> ProgNode {
        enum Item {
            Convert(Arc<TranslationNode>),
            MakeTake,
            MakeDrop,
            MakePair,
        }

        let mut stack = vec![Item::Convert(self)];
        let mut output = vec![];

        // We iterate over the tree in pre-order.
        // However, we change the tree as we iterate,
        // so using `VerbosePreOrderIter` seems impossible.
        while let Some(top) = stack.pop() {
            match top {
                Item::Convert(node) => match node.as_ref() {
                    TranslationNode::Unit => {
                        output.push(ProgNode::unit());
                    }
                    TranslationNode::Short(vec) => {
                        let mut expr = ProgNode::iden();
                        for short in vec.iter().rev() {
                            match short {
                                Short::O => expr = ProgNode::take(expr),
                                Short::I => expr = ProgNode::drop_(expr),
                            }
                        }
                        output.push(expr);
                    }
                    TranslationNode::Pair(l, r) => {
                        if let Some((new_l, new_r, short)) = node.eliminate_take_drop() {
                            match short {
                                Short::O => stack.push(Item::MakeTake),
                                Short::I => stack.push(Item::MakeDrop),
                            }
                            stack.push(Item::MakePair);
                            stack.push(Item::Convert(Arc::new(new_r)));
                            stack.push(Item::Convert(Arc::new(new_l)));
                        } else {
                            stack.push(Item::MakePair);
                            stack.push(Item::Convert(r.clone()));
                            stack.push(Item::Convert(l.clone()));
                        }
                    }
                },
                Item::MakePair => {
                    let expr_r = output.pop().unwrap();
                    let expr_l = output.pop().unwrap();
                    output.push(ProgNode::pair(expr_l, expr_r));
                }
                Item::MakeTake => {
                    let expr = output.pop().unwrap();
                    output.push(ProgNode::take(expr));
                }
                Item::MakeDrop => {
                    let expr = output.pop().unwrap();
                    output.push(ProgNode::drop_(expr));
                }
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::DisplayNode;

    #[test]
    fn pattern_translate() {
        let a = Pattern::Identifier(Identifier::from_str_unchecked("a"));
        let b = Pattern::Identifier(Identifier::from_str_unchecked("b"));
        let c = Pattern::Identifier(Identifier::from_str_unchecked("c"));
        let env = Pattern::array([a.clone(), b.clone(), c.clone()]);

        let target_expr = [
            (a.clone(), "take take iden"),
            (b.clone(), "take drop iden"),
            (c.clone(), "drop iden"),
            (Pattern::product(a.clone(), b.clone()), "take iden"),
            (
                Pattern::product(a.clone(), c.clone()),
                "pair (take take iden) (drop iden)",
            ),
            (
                Pattern::product(b.clone(), a.clone()),
                "take pair (drop iden) (take iden)",
            ),
            (
                Pattern::product(b.clone(), c.clone()),
                "pair (take drop iden) (drop iden)",
            ),
            (
                Pattern::product(c.clone(), a.clone()),
                "pair (drop iden) (take take iden)",
            ),
            (
                Pattern::product(c.clone(), b.clone()),
                "pair (drop iden) (take drop iden)",
            ),
            (env.clone(), "iden"),
            (
                Pattern::product(Pattern::product(a.clone(), b.clone()), Pattern::Ignore),
                "iden",
            ),
            (Pattern::product(Pattern::Ignore, c.clone()), "iden"),
        ];

        for (target, expected_expr) in target_expr {
            let expr = env.translate(&target).unwrap();
            assert_eq!(expected_expr, &DisplayNode::from(expr.as_ref()).to_string());
        }
    }
}
