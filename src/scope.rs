use crate::array::BinaryTree;
use crate::named::{PairBuilder, SelectorBuilder};
use crate::parse::{Identifier, Pattern, WitnessName};
use crate::ProgNode;
use miniscript::iter::{Tree, TreeLike};
use simplicity::node::CoreConstructible as _;
use std::collections::HashMap;
use std::sync::Arc;

/// Tracker of variable bindings and witness names.
///
/// Internally there is a stack of scopes.
/// A new scope is pushed for each (nested) block expression.
///
/// Bindings from higher scopes (in the stack) overwrite bindings from lower scopes.
#[derive(Debug, Clone)]
pub struct GlobalScope {
    variables: Vec<Vec<Pattern>>,
    witnesses: Vec<Vec<WitnessName>>,
}

impl Default for GlobalScope {
    fn default() -> Self {
        Self::new()
    }
}

impl GlobalScope {
    /// Creates a new [`GlobalScope`].
    pub fn new() -> Self {
        GlobalScope {
            variables: vec![Vec::new()],
            witnesses: vec![Vec::new()],
        }
    }

    /// Pushes a new scope to the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(Vec::new());
        self.witnesses.push(Vec::new());
    }

    /// Pops the latest scope from the stack.
    ///
    /// # Panics
    ///
    /// Panics if the stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Popping scope zero");
        self.witnesses.pop().expect("Popping scope zero");
    }

    /// Pushes a new variable to the latest scope.
    pub fn insert(&mut self, pattern: Pattern) {
        self.variables.last_mut().unwrap().push(pattern);
    }

    /// Pushes a new witness to the latest scope.
    pub fn insert_witness(&mut self, key: WitnessName) {
        self.witnesses.last_mut().unwrap().push(key);
    }

    /// Get a Simplicity expression that returns the value of the given `identifier`.
    ///
    /// The expression is a sequence of `take` and `drop` followed by `iden`,
    /// which extracts the seeked value from the environment.
    ///
    /// The environment starts as the unit value.
    ///
    /// Each let statement updates the environment to become
    /// the product of the assigned value (left) and of the previous environment (right).
    ///
    /// (Block) expressions consume the environment and return their output.
    ///
    /// ## Example
    ///
    /// ```
    /// let a: u8 = 0;
    /// let b = {
    ///     let b: u8 = 1;
    ///     let c: u8 = 2;
    ///     a  // here we seek the value of `a`
    /// };
    /// ```
    ///
    /// The stack of scopes looks like this:
    ///
    /// `[a] [b c]`
    ///
    /// The environment looks like this:
    ///
    /// ```text
    ///   .
    ///  / \
    /// C   .
    ///    / \
    ///   B   .
    ///      / \
    ///     A   1
    /// ```
    ///
    /// To extract `a`, we need the expression `drop drop take iden`.
    ///
    /// ## Error
    ///
    /// The `identifier` is undefined.
    pub fn get(&self, identifier: &Identifier) -> Option<ProgNode> {
        self.variables
            .iter()
            .rev() // Innermost scope has precedence
            .flat_map(|scope| scope.iter().rev()) // Last assignment has precedence
            .enumerate()
            .find_map(|(idx, pattern)| {
                pattern.get_program(identifier).map(|mut expr| {
                    expr = ProgNode::take(&expr);
                    for _ in 0..idx {
                        expr = ProgNode::drop_(&expr);
                    }
                    expr
                })
            })
    }
}

/// Basic structure of a Simfony value for pattern matching.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum BasePattern {
    /// Ignore: Match any value.
    ///
    /// Used for matching values that are not assigned to a variable.
    Ignore,
    /// Variable identifier: Match any value and bind it to an identifier.
    Identifier(Identifier),
    /// Product: Match product value component-wise.
    Product(Arc<Self>, Arc<Self>),
}

impl<'a> TreeLike for &'a BasePattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            BasePattern::Ignore | BasePattern::Identifier(_) => Tree::Nullary,
            BasePattern::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

impl BasePattern {
    /// Construct a product of patterns `left` and `right`.
    pub fn product(left: Self, right: Self) -> Self {
        Self::Product(Arc::new(left), Arc::new(right))
    }

    /// Access the identifier inside an identifier pattern.
    pub fn as_identifier(&self) -> Option<&Identifier> {
        match self {
            Self::Identifier(identifier) => Some(identifier),
            _ => None,
        }
    }

    /// Check if the `identifier` is contained inside the pattern.
    pub fn contains(&self, identifier: &Identifier) -> bool {
        self.pre_order_iter().any(|sub_pattern| {
            sub_pattern
                .as_identifier()
                .map(|sub_id| sub_id == identifier)
                .unwrap_or(false)
        })
    }

    /// Compute a Simplicity expression that returns the value of the given `identifier`.
    /// The expression takes as input a value that matches the `self` pattern.
    ///
    /// The expression is a sequence of `take` and `drop` followed by `iden`.
    fn get(mut self: &Self, identifier: &Identifier) -> Option<SelectorBuilder<ProgNode>> {
        let mut selector = SelectorBuilder::default();
        loop {
            // Termination: self becomes strictly smaller in each iteration
            match self {
                BasePattern::Identifier(self_id) if self_id == identifier => return Some(selector),
                BasePattern::Identifier(_) | BasePattern::Ignore => return None,
                BasePattern::Product(self_left, self_right) => {
                    if self_left.contains(identifier) {
                        selector = selector.o();
                        self = self_left;
                    } else if self_right.contains(identifier) {
                        selector = selector.i();
                        self = self_right;
                    } else {
                        return None;
                    }
                }
            }
        }
    }
}

impl From<&Pattern> for BasePattern {
    fn from(pattern: &Pattern) -> Self {
        let binary = BinaryTree::from_tree(pattern);
        let mut to_base = HashMap::new();

        for data in binary.clone().post_order_iter() {
            match data.node.as_node() {
                Tree::Nullary => {
                    let pattern = match &data.node.as_normal().unwrap() {
                        Pattern::Identifier(id) => BasePattern::Identifier(id.clone()),
                        Pattern::Ignore => BasePattern::Ignore,
                        Pattern::Product(..) | Pattern::Array(..) => unreachable!("Nullary node"),
                    };
                    to_base.insert(data.node, pattern);
                }
                Tree::Binary(l, r) => {
                    let l_converted = to_base.get(&l).unwrap().clone();
                    let r_converted = to_base.get(&r).unwrap().clone();
                    let pattern = BasePattern::product(l_converted, r_converted);
                    to_base.insert(data.node, pattern);
                }
                Tree::Unary(..) => unreachable!("There are no unary patterns"),
                Tree::Nary(..) => unreachable!("Binary trees have no arrays"),
            }
        }

        to_base.remove(&binary).unwrap()
    }
}

impl Pattern {
    pub fn get_program(&self, identifier: &Identifier) -> Option<ProgNode> {
        BasePattern::from(self)
            .get(identifier)
            .map(SelectorBuilder::h)
            .map(PairBuilder::get)
    }
}
