//! This module implements a structure for representing tree-child networks in a form ready to be
//! translated to extended Newick format.

use tree_child_sequence::{Pair, TcSeq};

/// A structure to represent a tree-child network
pub struct TcNet<T> {
    dummy: TcSeq<T>,
}

impl<T> TcNet<T> {

    /// Create a tree-child network from a given tree-child sequence
    pub fn from_seq(seq: TcSeq<T>) -> Self {
        Self { dummy: seq }
    }
}
