use simplicity::node::CoreConstructible;

use crate::ProgNode;

/// A global scope is a stack of scopes.
/// Each scope is a vector of variables.
/// The latest scope is the last vector in the stack.
///
/// Our simplicity translation looks at the index
/// of the variable from the end of stack to figure it's
/// position in the environment.
#[derive(Debug)]
pub struct GlobalScope {
    variables: Vec<Vec<String>>,
}

impl GlobalScope {
    /// Creates a new [`GlobalScope`].
    pub fn new() -> Self {
        GlobalScope {
            variables: vec![Vec::new()],
        }
    }

    /// Pushes a new scope to the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(Vec::new());
    }

    /// Pops the latest scope from the stack.
    ///
    /// # Panics
    ///
    /// Panics if the stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Popping scope zero");
    }

    /// Pushes a new variable to the latest scope.
    pub fn insert(&mut self, key: String) {
        self.variables.last_mut().unwrap().push(key);
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
    pub fn get(&self, key: &str) -> ProgNode {
        // search in the vector of vectors from the end
        let mut pos = 0;
        let mut found = false;
        for v in self.variables.iter().rev() {
            if let Some(idx) = v.iter().rev().position(|var_name| var_name == key) {
                pos += idx;
                found = true;
                break;
            } else {
                pos += v.len();
            }
        }
        if !found {
            panic!("Variable {} not found", key);
        }
        let mut child = ProgNode::iden();
        child = ProgNode::drop_(&child);
        for _ in 0..pos {
            child = ProgNode::take(&child);
        }
        // println!("Fetching for variable {key} as {pos}, {child:?}");
        child
    }
}
