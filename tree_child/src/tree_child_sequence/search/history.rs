use std::vec;

use super::cherry;
use tree::{Leaf, Node};

/// The history of operations applied to produce the current set of trees
#[derive(Clone)]
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

    /// Clear the history
    pub fn clear(&mut self) {
        self.0.clear();
    }
}


/// The operations we perform
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
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

    /// Record a new cherry and remember which cherry took its place if it was moved from the
    /// non-trivial cherry list to the trivial cherry list
    RecordCherry(cherry::Ref, Option<cherry::Ref>),

    /// Prune a leaf from a tree
    PruneLeaf(Leaf, usize),

    /// Suppress a node from a tree
    SuppressNode(Node, usize),

    /// Add a cherry to the tree-child sequence
    PushTreeChildPair,

    /// Increase the recorded weight of the current tree-child sequence
    IncreaseWeight,

    /// Record a cut operation performed to resolve a cherry.  To undo this, we need to know
    /// whether the first or second leaf of the cherry was cut (bool is true if it's the first),
    /// and the original cut count before the cut.
    Cut(cherry::Ref, bool, usize),
}


/// A snapshot of the current search state
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
#[derive(Clone, Copy)]
pub struct Snapshot(usize);


#[cfg(test)]
pub mod tests {

    use super::*;

    /// Test history operations
    #[test]
    fn history() {
        let mut history = History::new();
        assert!(history.0.is_empty());
        history.record_op(Op::PushTrivialCherry);
        history.record_op(Op::PushTreeChildPair);
        let snapshot1 = history.take_snapshot();
        assert_eq!(snapshot1.0, 2);
        history.record_op(Op::IncreaseWeight);
        history.record_op(Op::PushTrivialCherry);
        let snapshot2 = history.take_snapshot();
        assert_eq!(history.0, vec![Op::PushTrivialCherry, Op::PushTreeChildPair,
                   Op::IncreaseWeight, Op::PushTrivialCherry]);
        assert_eq!(snapshot2.0, 4);
        history.record_op(Op::PushTrivialCherry);
        assert_eq!(history.0, vec![Op::PushTrivialCherry, Op::PushTreeChildPair,
                   Op::IncreaseWeight, Op::PushTrivialCherry, Op::PushTrivialCherry]);
        let undo2 = history.rewind(snapshot2).collect::<Vec<Op>>();
        assert_eq!(history.0, vec![Op::PushTrivialCherry, Op::PushTreeChildPair,
                   Op::IncreaseWeight, Op::PushTrivialCherry]);
        assert_eq!(undo2, vec![Op::PushTrivialCherry]);
        let undo1 = history.rewind(snapshot1).collect::<Vec<Op>>();
        assert_eq!(history.0, vec![Op::PushTrivialCherry, Op::PushTreeChildPair]);
        assert_eq!(undo1, vec![Op::PushTrivialCherry, Op::IncreaseWeight]);
    }

    /// Helper methods for inspecting the internal state of the history
    pub fn ops(history: &History) -> &Vec<Op> {
        &history.0
    }
}
