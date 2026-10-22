use std::collections::HashMap;

use crate::str::Identifier;
use crate::types::ResolvedType;

/// Variables of the function that is being analyzed.
#[derive(Default)]
pub(super) struct Locals {
    /// Block-level variable scopes. Push on block enter, pop on block exit.
    blocks: Vec<HashMap<Identifier, ResolvedType>>,
}

impl Locals {
    /// Number of open blocks, zero outside a function.
    pub(super) fn depth(&self) -> usize {
        self.blocks.len()
    }

    /// Enter a new block inside the current function.
    pub(super) fn enter_block(&mut self) {
        self.blocks.push(HashMap::new());
    }

    /// Exit the current block inside the current function.
    ///
    /// ## Panics
    ///
    /// - No acive block to exit.
    pub(super) fn exit_block(&mut self) {
        self.blocks.pop().expect("No active block to exit");
    }

    /// Insert a variable into the current block.
    ///
    /// ## Panics
    ///
    /// - No active block.
    pub(super) fn insert(&mut self, identifier: Identifier, ty: ResolvedType) {
        self.blocks
            .last_mut()
            .expect("Stack is empty")
            .insert(identifier, ty);
    }

    /// Get the type of the variable.
    pub(super) fn get(&self, identifier: &Identifier) -> Option<&ResolvedType> {
        self.blocks
            .iter()
            .rev()
            .find_map(|scope| scope.get(identifier))
    }
}
