mod cherry;
mod leaf;
mod history;
mod state;

use tree::{Tree, Leaf, Node};
use self::history::{History, Op, Snapshot};
use self::state::State;

/// The state of the search for a tree-child sequence
pub struct Search<T> {

    /// The current state of the search
    state: State<T>,

    /// The history of operations performed on the current search path, so they can be undone
    history: History,
}

impl<T> Search<T> {

    //----------------------------------------------------------------------------------------------
    // Initialization code
    //----------------------------------------------------------------------------------------------

    /// Create a new search state
    pub fn new(trees: Vec<Tree<T>>) -> Self {
        Search {
            state:   State::new(trees),
            history: History::new(),
        }
    }

    //----------------------------------------------------------------------------------------------
    // Running the search
    //----------------------------------------------------------------------------------------------


    /// Search for a tree-child sequence of weight k.
    pub fn run(mut self) -> super::TcSeq {
        self.resolve_trivial_cherries();
        while !self.recurse() {
            self.state.increase_max_weight();
        }
        self.state.tc_seq()
    }

    /// Recursively search for a tree-child sequence
    fn recurse(&mut self) -> bool {
        if let Some(leaf) = self.state.final_leaf() {
            // If there is only one leaf left, we have found a tree-child sequence and report
            // success after pushing the final pair to the tree-child sequence.
            self.state.push_final_tree_child_pair(leaf);
            true
        } else {
            // If there is more than one leaf left, we need to try to resolve non-trivial cherries
            // and recursively continue the search.

            if self.state.weight() < self.state.max_weight() {
                // If we haven't reached the maximum weight of an acceptable tree-child sequence in
                // the current search, try branching.

                if self.state.num_non_trivial_cherries() > 4*self.state.max_weight() {
                    // If there are more than 4*max_weight cherries to branch on, then the
                    // tree-child hybridization number is greater than max_weight, abort.
                    false
                } else {
                    // Otherwise, branch.
                    let snapshot = self.history.take_snapshot();
                    for index in 0..self.state.num_non_trivial_cherries() {
                        let cherry = self.remove_cherry(cherry::Ref::NonTrivial(index));
                        let (u, v) = cherry.leaves();
                        if self.state.leaf(v).num_occurrences() == self.state.num_trees() {
                            self.increase_weight();
                            self.push_tree_child_pair(u, v);
                            for tree in cherry.trees() {
                                self.prune_leaf(u, *tree);
                            }
                            if self.recurse() {
                                return true;
                            }
                            self.rewind_to_snapshot(snapshot);
                        }
                        if self.state.leaf(u).num_occurrences() == self.state.num_trees() {
                            self.increase_weight();
                            self.push_tree_child_pair(v, u);
                            for tree in cherry.trees() {
                                self.prune_leaf(v, *tree);
                            }
                            if self.recurse() {
                                return true;
                            }
                            self.rewind_to_snapshot(snapshot);
                        }
                    }
                    false
                }

            } else {
                // If we have reached the maximum weight of an acceptable tree-child sequence in
                // the current search, report failure in this branch
                false
            }
        }
    }

    /// Eliminate all trivial cherries in the current search state.
    fn resolve_trivial_cherries(&mut self) {
        while let Some(cherry) = self.pop_trivial_cherry() {

            // Order the elements of the cherry so v is guaranteed to be in all
            // trees.  (This is true for at least one of u and v).
            let (u, v) = {
                let (u, v) = cherry.leaves();
                if self.state.leaf(v).num_occurrences() < self.state.num_trees() {
                    (v, u)
                } else {
                    (u, v)
                }
            };

            // Add (u, v) as a cherry to the cherry picking sequence
            self.push_tree_child_pair(u, v);

            // Prune u from every tree that has the cherry (u, v)
            for tree in cherry.trees() {
                self.prune_leaf(u, *tree);
            }
        }
    }

    /// Rewind to a snapshot
    fn rewind_to_snapshot(&mut self, snapshot: Snapshot) {
        for op in self.history.rewind(snapshot) {
            match op {
                Op::PushTrivialCherry                     => self.undo_push_trivial_cherry(),
                Op::PopTrivialCherry(cherry)              => self.undo_pop_trivial_cherry(cherry),
                Op::RemoveTrivialCherry(index, cherry)    => self.undo_remove_trivial_cherry(index, cherry),
                Op::RemoveNonTrivialCherry(index, cherry) => self.undo_remove_non_trivial_cherry(index, cherry),
                Op::RecordCherry(cherry_ref)              => self.undo_record_cherry(cherry_ref),
                Op::PruneLeaf(leaf, tree)                 => self.undo_prune_leaf(leaf, tree),
                Op::SuppressNode(node, tree)              => self.undo_suppress_node(node, tree),
                Op::PushTreeChildPair                     => self.undo_push_tree_child_pair(),
                Op::IncreaseWeight                        => self.undo_increase_weight(),
            }
        }
    }

    //----------------------------------------------------------------------------------------------
    // Operations on cherries
    //----------------------------------------------------------------------------------------------

    /// Record a newly detected cherry
    fn record_cherry(&mut self, u: Leaf, v: Leaf, tree: usize) {
        let cherry_ref = self.state.record_cherry(u, v, tree);
        self.history.record_op(Op::RecordCherry(cherry_ref));
    }

    /// Undo recording a cherry
    fn undo_record_cherry(&mut self, cherry_ref: cherry::Ref) {
        self.state.forget_cherry(cherry_ref);
    }

    /// Push a cherry to the end of the list of trivial cherries
    fn push_trivial_cherry(&mut self, cherry: cherry::Cherry) {
        self.history.record_op(Op::PushTrivialCherry);
        self.state.push_trivial_cherry(cherry);
    }

    /// Undo pushing a trivial cherry
    fn undo_push_trivial_cherry(&mut self) {
        self.state.pop_trivial_cherry();
    }

    /// Pop the last cherry from the list of trivial cherries
    fn pop_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.state.pop_trivial_cherry().map(|cherry| {
            self.history.record_op(Op::PopTrivialCherry(cherry.clone()));
            cherry
        })
    }

    /// Undo popping a trivial cherry
    fn undo_pop_trivial_cherry(&mut self, cherry: cherry::Cherry) {
        self.state.push_trivial_cherry(cherry);
    }

    /// Remove a cherry indexed by the given cherry reference
    fn remove_cherry(&mut self, cherry_ref: cherry::Ref) -> cherry::Cherry {
        let cherry = self.state.remove_cherry(cherry_ref);

        match cherry_ref {

            cherry::Ref::Trivial(ix) => {
                self.history.record_op(Op::RemoveTrivialCherry(ix, cherry.clone()));
            },

            cherry::Ref::NonTrivial(ix) => {
                self.history.record_op(Op::RemoveNonTrivialCherry(ix, cherry.clone()));
            },
        }

        cherry
    }

    /// Undo the removal of a trivial cherry
    fn undo_remove_trivial_cherry(&mut self, ix: usize, cherry: cherry::Cherry) {
        self.state.restore_trivial_cherry(ix, cherry);
    }

    /// Undo the removal of a non-trivial cherry
    fn undo_remove_non_trivial_cherry(&mut self, ix: usize, cherry: cherry::Cherry) {
        self.state.restore_non_trivial_cherry(ix, cherry);
    }

    //----------------------------------------------------------------------------------------------
    // Operations on the trees
    //----------------------------------------------------------------------------------------------

    /// Prune a leaf from a given tree
    fn prune_leaf(&mut self, leaf: Leaf, tree: usize) {

        // Prune the leaf and suppress the parent if it exists
        self.history.record_op(Op::PruneLeaf(leaf, tree));
        if let Some(parent) = self.state.prune_leaf(leaf, tree) {
            self.suppress_node(parent, tree);
        }

        // Check whether this has created a new trivial cherry
        if let Some(cherry_ref) = self.state.check_for_trivial_cherry(leaf) {
            let cherry = self.remove_cherry(cherry_ref);
            self.push_trivial_cherry(cherry);
        }
    }

    /// Undo the pruning of a leaf
    fn undo_prune_leaf(&mut self,leaf: Leaf, tree: usize) {
        self.state.restore_leaf(leaf, tree);
    }

    /// Suppress a node
    fn suppress_node(&mut self, node: Node, tree: usize) {

        // Suppress the node
        self.history.record_op(Op::SuppressNode(node, tree));
        let child = self.state.suppress_node(node, tree);

        // Check whether this has created a new cherry
        if let Some((u, v)) = self.state.check_for_cherry(child, tree) {
            self.record_cherry(u, v, tree);
        }
    }

    /// Undo the suppression of a node
    fn undo_suppress_node(&mut self, node: Node, tree: usize) {
        self.state.restore_node(node, tree);
    }

    //----------------------------------------------------------------------------------------------
    // Operations on the tree-child sequence
    //----------------------------------------------------------------------------------------------

    /// Add a cherry to the cherry picking sequence
    fn push_tree_child_pair(&mut self, u: Leaf, v: Leaf) {
        self.history.record_op(Op::PushTreeChildPair);
        self.state.push_tree_child_pair(u, v);
    }

    /// Undo the recording of a cherry
    fn undo_push_tree_child_pair(&mut self) {
        self.state.pop_tree_child_pair();
    }

    /// Increase the weight of the current sequence
    fn increase_weight(&mut self) {
        self.history.record_op(Op::IncreaseWeight);
        self.state.increase_weight();
    }

    /// Undo a weight increase
    fn undo_increase_weight(&mut self) {
        self.state.decrease_weight();
    }
}
