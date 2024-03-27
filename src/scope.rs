use miniscript::iter::TreeLike;

use crate::parse::{Identifier, Pattern, WitnessName};
use crate::{named::ProgExt, ProgNode};

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
    /// ## Panics
    ///
    /// The `identifier` is undefined.
    pub fn get(&self, identifier: &Identifier) -> ProgNode {
        let mut pos = 0;
        let mut var = None;
        for v in self.variables.iter().rev() {
            if let Some(idx) = v
                .iter()
                .rev()
                .position(|var_name| var_name.contains(identifier))
            {
                pos += idx;
                var = Some(&v[v.len() - 1 - idx]);
                break;
            } else {
                pos += v.len();
            }
        }
        match var {
            Some(pattern) => {
                let mut child = pattern.get_program(identifier).unwrap();
                child = ProgNode::take(child);
                for _ in 0..pos {
                    child = ProgNode::drop_(child);
                }
                child
            }
            None => panic!("Variable {} not found", identifier),
        }
    }
}

impl Pattern {
    pub fn get_identifier(&self) -> Option<&Identifier> {
        match self {
            Pattern::Identifier(i) => Some(i),
            _ => None,
        }
    }

    pub fn contains(&self, identifier: &Identifier) -> bool {
        self.pre_order_iter().any(|pattern| {
            pattern
                .get_identifier()
                .map(|i| i == identifier)
                .unwrap_or(false)
        })
    }

    pub fn get_program(&self, identifier: &Identifier) -> Option<ProgNode> {
        enum Direction {
            Left,
            Right,
        }

        let mut pattern = self;
        let mut path = vec![];

        loop {
            match pattern {
                Pattern::Identifier(i) => {
                    if i == identifier {
                        break;
                    } else {
                        return None;
                    }
                }
                Pattern::Ignore => return None,
                Pattern::Product(l, r) => {
                    if l.contains(identifier) {
                        path.push(Direction::Left);
                        pattern = l;
                    } else {
                        // Avoid checking if right branch contains identifier
                        // We will find out once we reach the leaf
                        path.push(Direction::Right);
                        pattern = r;
                    }
                }
            }
        }

        let mut output = ProgNode::iden();
        while let Some(direction) = path.pop() {
            match direction {
                Direction::Left => output = ProgNode::take(output),
                Direction::Right => output = ProgNode::drop_(output),
            }
        }

        Some(output)
    }
}
