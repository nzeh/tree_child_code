//! This module implements the algorithm for constructing a tree-child sequence for a set of trees.
//! The function to construct a tree-child sequence is `tree_child_sequence()`.

use std::fmt;
use tree::Tree;

mod search;

/// An entry in a tree-child sequence
#[derive(Debug, Eq, PartialEq)]
pub enum Pair<T> {

    /// A pair (x, y) that eliminates x from every tree that has (x, y) as a cherry
    Reduce(T, T),

    /// The final leaf left in every tree at the end of the sequence
    Final(T),
}


/// A tree-child sequence is just a sequence of `Pair`s
pub type TcSeq<T> = Vec<Pair<T>>;


/// Compute a tree-child sequence for a given set of trees
pub fn tree_child_sequence<T: Clone>(trees: Vec<Tree<T>>) -> TcSeq<T> {
    search::Search::new(trees).run()
}

/// Let's make pairs printable
impl<T: fmt::Display> fmt::Display for Pair<T> {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Pair::Reduce(u, v) => write!(f, "({}, {})", u, v),
            Pair::Final(u)     => write!(f, "({}, -)", u),
        }
    }
}
