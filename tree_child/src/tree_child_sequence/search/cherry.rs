use std::slice;

use tree::Leaf;

/// The data associated with a cherry
#[derive(Clone)]
pub struct Cherry {

    /// The first leaf of this cherry
    u: Leaf,

    /// The second leaf of this cherry
    v: Leaf,

    /// The position of this cherry in the first leaf's cherry list
    uix: usize,

    /// The position of this cherry in the second leaf's cherry list
    vix: usize,

    /// The trees that have this cherry
    trees: Vec<usize>,
}

/// Reference to a cherry
#[derive(Clone, Copy)]
pub enum Ref {
    Trivial(usize),
    NonTrivial(usize),
}

impl Cherry {

    /// Remove the final tree this cherry occurs in
    pub fn pop_tree(&mut self) {
        self.trees.pop();
    }

    /// The trees that have this cherry
    pub fn trees(&self) -> slice::Iter<usize> {
        self.trees.iter()
    }

    /// The number of tress this cherry occurs in
    pub fn num_occurrences(&self) -> usize {
        self.trees.len()
    }

    /// The two leaves that make up this cherry
    pub fn leaves(&self) -> (Leaf, Leaf) {
        (self.u, self.v)
    }

    /// The indices of the references to this cherry in the leaves' cherry lists
    pub fn indices(&self) -> (usize, usize) {
        (self.uix, self.vix)
    }

    /// Update the indices of the references to this cherry in the leaves' cherry lists
    pub fn set_indices(&mut self, uix: usize, vix: usize) {
        self.uix = uix;
        self.vix = vix;
    }

    /// Set the index for the given leaf
    pub fn set_index(&mut self, leaf: Leaf, ix: usize) {
        if leaf == self.u {
            self.uix = ix;
        } else {
            self.vix = ix;
        }
    }
}
