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

    /// Take a snapshot of the current history state
    pub fn take_snapshot(&self) -> Snapshot {
        Snapshot(self.0.len())
    }
}


/// The operations we perform
#[derive(Clone)]
pub enum Op {

    /// Add a cherry to the list of trivial cherries
    PushTrivialCherry,

    /// Remove a cherry from the end of the list of trivial cherries
    PopTrivialCherry(cherry::Cherry),

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
    PushTreeChildPair,

    /// Increase the recorded weight of the current tree-child sequence
    IncreaseWeight,
}


/// A snapshot of the current search state
#[derive(Clone, Copy)]
pub struct Snapshot(usize);
