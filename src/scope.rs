use crate::array::{DirectedTree, Direction};
use crate::parse::{Identifier, Pattern};
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
        }
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(Vec::new());
    }

    /// Pop a scope from the stack.
    ///
    /// # Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Empty stack");
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

    /// Get a Simplicity expression that returns the value of a variable.
    ///
    /// The expression takes the current input value and returns the seeked value.
    ///
    /// ## Example
    ///
    /// ```text
    /// let a: u8 = 0;
    /// let b = {
    ///     let b: u8 = 1;
    ///     let c: u8 = 2;
    ///     a  // here we seek the value of `a`
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
    /// The expression `drop drop take iden` returns the value `0` for variable `a`.
    ///
    /// ## Panics
    ///
    /// The variable is not defined.
    pub fn get(&self, identifier: &Identifier) -> ProgNode {
        let mut pos = 0;

        // Highest scope has precedence
        for scope in self.variables.iter().rev() {
            // Last let statement has precedence
            if let Some((pattern_pos, mut expr)) =
                scope.iter().rev().enumerate().find_map(|(idx, pattern)| {
                    pattern.get_program(identifier).map(|expr| (idx, expr))
                })
            {
                pos += pattern_pos;

                expr = ProgNode::take(expr);
                for _ in 0..pos {
                    expr = ProgNode::drop_(expr);
                }

                return expr;
            } else {
                pos += scope.len();
            }
        }

        panic!("\"{identifier}\" is undefined");
    }
}

impl Pattern {
    pub fn get_identifier(&self) -> Option<&Identifier> {
        match self {
            Pattern::Identifier(i) => Some(i),
            _ => None,
        }
    }

    pub fn get_program(&self, identifier: &Identifier) -> Option<ProgNode> {
        let base_pattern = self.to_base();
        let directed_tree = DirectedTree::from(&base_pattern);
        let equals_identifier = |pattern: &Pattern| {
            pattern
                .get_identifier()
                .map(|i| i == identifier)
                .unwrap_or(false)
        };
        let (_, mut path) = directed_tree.find(equals_identifier)?;

        let mut output = ProgNode::iden();
        while let Some(direction) = path.pop() {
            match direction {
                Direction::Left => output = ProgNode::take(output),
                Direction::Right => output = ProgNode::drop_(output),
                Direction::Down => unreachable!("There are no unary patterns"),
                Direction::Index(..) => unreachable!("Base patterns exclude arrays"),
            }
        }

        Some(output)
    }
}
