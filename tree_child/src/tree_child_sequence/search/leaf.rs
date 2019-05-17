//! This module implements basic operations on leaves during the search.

use super::cherry;
use std::slice;

/// The data associated with a leaf
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
#[derive(Clone)]
pub struct Leaf {
    /// The number of trees this leaf still occurs in
    num_occurrences: usize,

    /// The number of times this leaf has been pruned
    times_pruned: usize,

    /// The cherries this leaf is part of
    cherries: Vec<cherry::Ref>,
}

impl Leaf {
    /// Create a new leaf occurring in the given number of trees
    pub fn new(num_occurrences: usize) -> Self {
        Self {
            num_occurrences,
            times_pruned: 0,
            cherries: vec![],
        }
    }

    /// Increase the number of occurrences of this leaf
    pub fn increase_num_occurrences(&mut self) {
        self.num_occurrences += 1;
    }

    /// Decrease the number of occurrences of this leaf
    pub fn decrease_num_occurrences(&mut self) {
        self.num_occurrences -= 1;
    }

    /// The number of occurrences of this leaf
    pub fn num_occurrences(&self) -> usize {
        self.num_occurrences
    }

    /// Increase the count of how often this leaf has been pruned
    pub fn increase_times_pruned(&mut self) {
        self.times_pruned += 1;
    }

    /// Decrease the count of how often this leaf has been pruned
    pub fn decrease_times_pruned(&mut self) {
        self.times_pruned -= 1;
    }

    /// The number of times this leaf has been pruned
    pub fn times_pruned(&self) -> usize {
        self.times_pruned
    }

    /// The number of cherries this leaf participates in
    pub fn num_cherries(&self) -> usize {
        self.cherries.len()
    }

    /// Access the `ix`th cherry ref in this leaf's cherry list
    pub fn cherry(&self, ix: usize) -> cherry::Ref {
        self.cherries[ix]
    }

    /// Provide a mutable reference to the `ix`th cherry in this leaf's cherry list
    pub fn cherry_mut(&mut self, ix: usize) -> &mut cherry::Ref {
        &mut self.cherries[ix]
    }

    /// Add a new cherry
    pub fn add_cherry(&mut self, cherry_ref: cherry::Ref) {
        self.cherries.push(cherry_ref)
    }

    /// Remove a cherry
    pub fn remove_cherry(&mut self, ix: usize) {
        self.cherries.swap_remove(ix);
    }

    /// Update the `ix`th cherry ref with a new reference (to reflect that this cherry was moved)
    pub fn replace_cherry(&mut self, ix: usize, cherry_ref: cherry::Ref) {
        self.cherries[ix] = cherry_ref;
    }

    /// Iterator over the cherries this leaf participates in
    pub fn cherries(&self) -> slice::Iter<cherry::Ref> {
        self.cherries.iter()
    }
}
