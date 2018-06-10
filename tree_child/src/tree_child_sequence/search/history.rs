use std::vec;

use super::cherry;
use tree::{Leaf, Node};

/// The history of operations applied to produce the current set of trees
pub struct History(Vec<Op>);


impl History {

    /// Create a new empty history
    pub fn new() -> History {
        History(vec![])
    }

    /// Record an operation
    pub fn record_op(&mut self, op: Op) {
        self.0.push(op);
    }

    /// An iterator over the operations to unwind
    pub fn rewind(&mut self, snapshot: Snapshot) -> vec::IntoIter<Op> {
        let mut ops = vec![];
        while self.0.len() > snapshot.0 {
            ops.push(self.0.pop().unwrap());
        }
        ops.into_iter()
    }
}


/// The operations we perform
#[derive(Clone)]
pub enum Op {

    /// Add a cherry to the list of trivial cherries
    AddTrivialCherry,

    /// Add a cherry to the list of non-trivial cherries
    AddNonTrivialCherry,

    /// Remove a cherry from the end of the list of trivial cherries
    PopTrivialCherry(cherry::Cherry),

    /// Remove a cherry from the end of the list of non-trivial cherries
    PopNonTrivialCherry(cherry::Cherry),

    /// Remove a cherry from the list of trivial cherries
    RemoveTrivialCherry(usize, cherry::Cherry),

    /// Remove a cherry from the list of non-trivial cherries
    RemoveNonTrivialCherry(usize, cherry::Cherry),

    /// Record a new cherry
    RecordCherry(cherry::Ref),

    /// Prune a leaf from a tree
    PruneLeaf(Leaf, usize),

    /// Suppress a node from a tree
    SuppressNode(Node, usize),

    /// Add a cherry to the tree-child sequence
    RecordTreeChildPair,
}


/// A snapshot of the current search state
pub struct Snapshot(usize);
