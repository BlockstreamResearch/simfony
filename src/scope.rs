use miniscript::iter::TreeLike;

use crate::parse::{Identifier, Pattern, WitnessName};
use crate::{named::ProgExt, ProgNode};

/// A global scope is a stack of scopes.
/// Each scope is a vector of variables.
/// The latest scope is the last vector in the stack.
///
/// Our simplicity translation looks at the index
/// of the variable from the end of stack to figure it's
/// position in the environment.
#[derive(Debug)]
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

    /// Fetches the [`ProgNode`] for a variable.
    /// The [`ProgNode`] is a sequence of `take` and `drop` nodes
    /// that fetches the variable from the environment.
    /// The [`ProgNode`] is constructed by looking at the index
    /// of the variable from the end of stack.
    ///
    /// # Panics
    ///
    /// Panics if the variable is not found.
    pub fn get(&self, key: &Identifier) -> ProgNode {
        // search in the vector of vectors from the end
        let mut pos = 0;
        let mut var = None;
        for v in self.variables.iter().rev() {
            if let Some(idx) = v.iter().rev().position(|var_name| var_name.contains(key)) {
                pos += idx;
                var = Some(&v[v.len() - 1 - idx]);
                break;
            } else {
                pos += v.len();
            }
        }
        match var {
            Some(pattern) => {
                let mut child = pattern.get_program(key).unwrap();
                child = ProgNode::take(child);
                for _ in 0..pos {
                    child = ProgNode::drop_(child);
                }
                child
            }
            None => panic!("Variable {} not found", key),
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
