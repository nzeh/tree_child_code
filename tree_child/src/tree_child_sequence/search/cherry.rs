//! This module implements basic operations on cherries.

use std::mem;
use std::slice;
use tree::Leaf;

/// The data associated with a cherry
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
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

    /// The number of trees that contained this cherry the last time we cut u
    u_trees_cut: usize,

    /// The number of trees that contained this cherry the last time we cut v
    v_trees_cut: usize,

}

impl Cherry {

    /// Create a new cherry first found in `tree`
    pub fn new(u: Leaf, v: Leaf, tree: usize) -> Self {
        Self {
            u, v,
            uix:         0,
            vix:         0,
            trees:       vec![tree],
            u_trees_cut: 0,
            v_trees_cut: 0,
        }
    }

    /// Push a new tree to the list of trees that have this cherry
    pub fn push_tree(&mut self, tree: usize) {
        self.trees.push(tree);
    }

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

    /// Update the number of cuts for one of the leaves.  Since we cut the leaf in all trees that
    /// have this cherry, the new cut count for this leaf is the number of occurrences of this
    /// cherry.
    pub fn cut(&mut self, first_leaf: bool) {
        let count = self.num_occurrences();
        self.set_cut_count(first_leaf, count);
    }

    /// Reset the cut count of this cherry for the indicated leaf.  The leaf may not be part of
    /// cherry at all.  In this case, no reset happens.
    pub fn reset_cut_count(&mut self, w: Leaf) -> Option<(bool, usize)> {
        if self.u == w {
            Some((true, mem::replace(&mut self.u_trees_cut, 0)))
        } else if self.v == w {
            Some((false, mem::replace(&mut self.v_trees_cut, 0)))
        } else {
            None
        }
    }

    /// Set the cut count for the given leaf
    pub fn set_cut_count(&mut self, first_leaf: bool, count: usize) {
        if first_leaf {
            self.u_trees_cut = count;
        } else {
            self.v_trees_cut = count;
        }
    }

    /// Query the number of leaves the given leaf was cut in
    pub fn cut_count(&self, first_leaf: bool) -> usize {
        if first_leaf {
            self.u_trees_cut
        } else {
            self.v_trees_cut
        }
    }
}

/// Reference to a cherry
#[cfg_attr(test, derive(Debug, Eq))]
#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub enum Ref {

    /// Reference to a cherry in the list of trivial cherries
    Trivial(usize),

    /// Reference to a cherry in the list of non-trivial cherries
    NonTrivial(usize),
}
