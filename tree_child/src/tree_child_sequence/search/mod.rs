//! This module implements the search state, including the current ephemeral state of all the trees
//! and cherry lists (encoded in a `State` object), the history of how we got to the current state,
//! and configuration options controlling the limiting of the branching fanout and the elimination
//! of redundant branches.

mod cherry;
mod leaf;
mod history;
mod state;

use std::collections::VecDeque;
use tree::{Tree, Leaf, Node};
use self::history::{History, Op, Snapshot};
use self::state::State;
use super::TcSeq;

/// The state of the search for a tree-child sequence
#[derive(Clone)]
pub struct Search<T> {

    /// The current state of the search
    state: State<T>,

    /// The history of operations performed on the current search path, so they can be undone
    history: History,

    /// The stack of recursive calls.  Maintained explicitly so we can carve off one of the
    /// branches still to be explored at the top of the recursion, in order to pass it to a
    /// different thread.
    stack: VecDeque<BranchPoint>,

    /// Was the search successful?
    success: bool,

    /// Limit the fanout (on by default but can disable to see whether this is indeed correct)
    limit_fanout: bool,

    /// Use the redundant branch optimization (EXPERIMENTAL)
    use_redundant_branch_opt: bool,
}

impl<T: Clone> Search<T> {

    //----------------------------------------------------------------------------------------------
    // Initialization code
    //----------------------------------------------------------------------------------------------

    /// Create a new search state
    pub fn new(trees: Vec<Tree<T>>, limit_fanout: bool, use_redundant_branch_opt: bool) -> Self {
        Self {
            state:   State::new(trees),
            history: History::new(),
            stack:   VecDeque::new(),
            success: false,
            limit_fanout,
            use_redundant_branch_opt,
        }
    }

    //----------------------------------------------------------------------------------------------
    // Code for splitting off part of the work in this instance into a new instance
    //----------------------------------------------------------------------------------------------

    /// Split off part of the work of this search into a new instance
    pub fn split(&mut self) -> Option<Self> {

        while !self.stack.is_empty() {

            // Make a copy of this search
            let mut other_search = self.clone();

            // Skip the next top branch in this search
            self.skip_next_top_branch();

            // Limit the copy to the skipped top branch and return that branch unless it is not a
            // feasible branch
            if other_search.limit_to_next_top_branch() {
                return Some(other_search);
            }
        }

        // No feasible branches found, return nothing
        None
    }

    /// Make sure this search does not follow the next available branch at the topmost branch point
    fn skip_next_top_branch(&mut self) {

        // Skip the next top branch and record whether we've now skipped all top braches
        let all_branches_skipped = {
            let top_branch = &mut self.stack[0];
            top_branch.num_skipped_branches += 1;
            top_branch.num_skipped_branches == top_branch.num_branches_left
        };

        // If so, remove the topmost branch point
        if all_branches_skipped {
            self.stack.pop_front();
        }
    }

    /// Rewind this search to its topmost branch point and limit the search to the next available
    /// branch at this branch point
    fn limit_to_next_top_branch(&mut self) -> bool {

        // Pop all but the topmost branch point
        self.stack.truncate(1);

        // Go to the next branch at this branch point
        self.branch();

        // If this branch is feasible (it was pushed on the stack)
        if self.stack.len() > 1 {
            // ... forget how we got here and report success
            self.history.clear();
            self.stack.clear();
            true
        } else {
            // Otherwise, report failure.
            false
        }
    }

    //----------------------------------------------------------------------------------------------
    // Running the search
    //----------------------------------------------------------------------------------------------

    /// Check whether the search is done and push the final tree-child pair if this is the case.
    pub fn success(&mut self) -> bool {

        if let Some(leaf) = self.state.final_leaf() {

            // Only one leaf left.  Push it and record success.
            self.state.push_final_tree_child_pair(leaf);
            self.success = true;
            true

        } else {

            // Nope, not done yet because we have more than one leaf left.
            false
        }
    }

    /// The search can succeed only if we haven't reached the maximum weight yet and we have at
    /// most 4*max_weight non-trivial cherries (not checked if `self.limit_fanout` is unset).
    pub fn can_succeed(&self) -> bool {
        self.state.weight() < self.state.max_weight() &&
            (!self.limit_fanout ||
             self.state.num_non_trivial_cherries() <= 4*self.state.max_weight())
    }

    /// Create a new branch point and return a snapshot of the state at the time of the branch
    pub fn start_branch(&mut self) {

        let snapshot          = self.history.take_snapshot();
        let num_branches_left = 2 * self.state.num_non_trivial_cherries();

        self.stack.push_back(BranchPoint {
            snapshot,
            cherry:               0,
            first_leaf:           true,
            num_branches_left,
            num_skipped_branches: 0,
        });
    }

    /// Try the next branch and return true if there are more branches left to explore
    pub fn branch(&mut self) -> bool {

        // Get the next branch to explore
        if let Some((cherry, first_leaf, cut_count)) = self.next_branch_not_skipped() {

            // Order the leaves of the cherry so we cut the right leaf
            let (u, v) = cherry.leaves();
            let (u, v) = if first_leaf {
                (u, v)
            } else {
                (v, u)
            };

            // Cutting u is allowed only if v has not been cut yet and necessary only if u has not
            // been cut in all trees of the current cherry yet.
            if  self.state.leaf(v).num_occurrences() == self.state.num_trees() &&
                (!self.use_redundant_branch_opt || cut_count < cherry.num_occurrences()) {

                // Record the tree-child pair and cut u in all trees that have the cherry (u, v)
                self.increase_weight();
                self.push_tree_child_pair(u, v);
                for tree in cherry.trees() {
                    self.prune_leaf(u, *tree);
                }

                // Resolve all non-trivial-cherries this has created
                self.resolve_trivial_cherries();

                // If we found a solution, terminate the search
                if self.success() {
                    return false;
                }

                // If we can still succeed, then create a new branch point for the current state
                if  self.can_succeed() {
                    self.start_branch();
                }
            }
        }

        // We can keep going if the stack is not empty yet
        !self.stack.is_empty()
    }

    /// Get the next branch that should not be skipped
    fn next_branch_not_skipped(&mut self) -> Option<(cherry::Cherry, bool, usize)> {

        if self.stack.is_empty() {
            return None;
        }

        let (snapshot, num_skipped_branches) = {
            let branch_point = self.stack.back().unwrap();
            (branch_point.snapshot, branch_point.num_skipped_branches)
        };

        // Reset the state to the last snapshot at this branch point
        self.rewind_to_snapshot(snapshot);

        // Skip over branches that were moved to other threads
        for _ in 0..num_skipped_branches {
            self.next_branch();
        }

        // We skipped all branches that should be skipped
        self.stack.back_mut().unwrap().num_skipped_branches = 0;

        // The next branch is the one that we should recurse into
        let (cherry, first_leaf, cut_count) = self.next_branch();
        Some((self.remove_cherry(cherry::Ref::NonTrivial(cherry)), first_leaf, cut_count))
    }

    /// Get the next branch to evaluate or skip
    fn next_branch(&mut self) -> (usize, bool, usize) {
        let (cherry, first_leaf, num_branches_left) = {
            let branch_point = self.stack.back().unwrap();
            (branch_point.cherry, branch_point.first_leaf, branch_point.num_branches_left)
        };

        // Record that we're cutting the next leaf at this branch point and make sure next
        // time we rewind we do not reset this cut count
        let cut_count = self.cut(cherry::Ref::NonTrivial(cherry), first_leaf);
        {
            let branch_point = self.stack.back_mut().unwrap();
            branch_point.snapshot = self.history.take_snapshot();
        }

        if num_branches_left > 1 {
            let branch_point = self.stack.back_mut().unwrap();
            branch_point.num_branches_left -= 1;
            if first_leaf {
                branch_point.first_leaf = false;
            } else {
                branch_point.cherry += 1;
                branch_point.first_leaf = true;
            }
        } else {
            self.stack.pop_back();
        }

        // Now return the cherry to branch on, whether to branch on the first leaf and that
        // leaf's cut count
        (cherry, first_leaf, cut_count)
    }

    /// Eliminate all trivial cherries in the current search state.
    pub fn resolve_trivial_cherries(&mut self) {
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
                Op::PushTrivialCherry                  => self.undo_push_trivial_cherry(),
                Op::PopTrivialCherry(cherry)           => self.undo_pop_trivial_cherry(cherry),
                Op::RemoveCherry(cherry_ref, cherry)   => self.undo_remove_cherry(cherry_ref, cherry),
                Op::RecordCherry(recorded, moved)      => self.undo_record_cherry(recorded, moved),
                Op::PruneLeaf(leaf, tree)              => self.undo_prune_leaf(leaf, tree),
                Op::SuppressNode(node, tree)           => self.undo_suppress_node(node, tree),
                Op::PushTreeChildPair                  => self.undo_push_tree_child_pair(),
                Op::IncreaseWeight                     => self.undo_increase_weight(),
                Op::Cut(cherry, first_leaf, cut_count) => self.undo_cut(cherry, first_leaf, cut_count),
            }
        }
    }

    //----------------------------------------------------------------------------------------------
    // Operations on cherries
    //----------------------------------------------------------------------------------------------

    /// Record a newly detected cherry
    fn record_cherry(&mut self, u: Leaf, v: Leaf, tree: usize) {
        let (recorded, moved) = self.state.record_cherry(u, v, tree);
        self.history.record_op(Op::RecordCherry(recorded, moved));
    }

    /// Undo recording a cherry
    fn undo_record_cherry(&mut self, recorded: cherry::Ref, moved: Option<cherry::Ref>) {
        self.state.forget_cherry(recorded, moved);
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
        self.history.record_op(Op::RemoveCherry(cherry_ref, cherry.clone()));
        cherry
    }

    /// Undo the removal of a cherry
    fn undo_remove_cherry(&mut self, cherry_ref: cherry::Ref, cherry: cherry::Cherry) {
        self.state.restore_cherry(cherry_ref, cherry);
    }

    /// Record a cut of a leaf in a cherry
    fn cut(&mut self, cherry_ref: cherry::Ref, first_leaf: bool) -> usize {
        let cut_count = self.state.cut(cherry_ref, first_leaf);
        self.history.record_op(Op::Cut(cherry_ref, first_leaf, cut_count));
        cut_count
    }

    /// Undo cutting of a leaf
    fn undo_cut(&mut self, cherry_ref: cherry::Ref, first_leaf: bool, cut_count: usize) {
        self.state.restore_cut_count(cherry_ref, first_leaf, cut_count);
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

    /// Retrieve the tree-child sequence
    pub fn tc_seq(self) -> Option<TcSeq<T>> {
        if self.success {
            Some(self.state.tc_seq())
        } else {
            None
        }
    }

    /// Increase the maximum weight of a tree-child sequence we are willing to accept as a solution
    pub fn increase_max_weight(&mut self) {
        self.state.increase_max_weight();
    }

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

/// A branch point is defined by a snapshot of the state before the branch, an index of the
/// non-trivial cherry to resolve next, and a Boolean flag that indicates whether we're cutting
/// the first leaf.
#[derive(Clone)]
struct BranchPoint {

    /// The history snapshot before branching
    snapshot: Snapshot,

    /// The index of the cherry to resolve
    cherry: usize,

    /// Are we branching on the first leaf of the cherry?
    first_leaf: bool,

    /// Number of branches left to explore
    num_branches_left: usize,

    /// Number of branches that were moved to other threads
    num_skipped_branches: usize,
}

#[cfg(test)]
mod tests {

    use newick;
    use super::*;
    use super::super::Pair;

    /// Test that the initial search state is initialized correctly
    #[test]
    fn new() {

        let (trees, newicks) = state::tests::build_forest();
        let search           = Search::new(trees, true, true);

        state::tests::test_new(search.state, newicks);
        assert!(history::tests::ops(&search.history).is_empty());
    }

    /// Test that increase_weight and undo_increase_weight are correct counterparts of each other
    #[test]
    fn do_undo_increase_weight() {

        let (trees, _) = state::tests::build_forest();
        let mut search = Search::new(trees, true, true);

        let snapshot = search.history.take_snapshot();

        search.increase_weight();

        assert_eq!(search.state.weight(), 1);
        assert_eq!(history::tests::ops(&search.history), &vec![history::Op::IncreaseWeight]);

        search.rewind_to_snapshot(snapshot);

        assert_eq!(search.state.weight(), 0);
        assert!(history::tests::ops(&search.history).is_empty());
    }

    /// Test that push_tree_child_pair and undo_push_tree_child_pair are correct counterparts of
    /// each other
    #[test]
    fn do_undo_push_tree_child_pair() {

        let (trees, _) = state::tests::build_forest();
        let mut search = Search::new(trees, true, true);

        let snapshot0 = search.history.take_snapshot();

        let u1 = Leaf::new(4);
        let v1 = Leaf::new(3);
        let u2 = Leaf::new(1);
        let v2 = Leaf::new(5);
        let u3 = Leaf::new(1);
        let v3 = Leaf::new(6);

        search.push_tree_child_pair(u1, v1);

        assert_eq!(history::tests::ops(&search.history), &vec![history::Op::PushTreeChildPair]);
        assert_eq!(state::tests::tc_seq(&search.state), &vec![Pair::Reduce(u1, v1)]);

        let snapshot1 = search.history.take_snapshot();

        search.push_tree_child_pair(u2, v2);
        search.push_tree_child_pair(u3, v3);

        assert_eq!(history::tests::ops(&search.history), &vec![
                   history::Op::PushTreeChildPair, history::Op::PushTreeChildPair,
                   history::Op::PushTreeChildPair]);
        assert_eq!(state::tests::tc_seq(&search.state), &vec![
                   Pair::Reduce(u1, v1),
                   Pair::Reduce(u2, v2),
                   Pair::Reduce(u3, v3)
        ]);

        search.rewind_to_snapshot(snapshot1);

        assert_eq!(history::tests::ops(&search.history), &vec![history::Op::PushTreeChildPair]);
        assert_eq!(state::tests::tc_seq(&search.state), &vec![Pair::Reduce(u1, v1)]);

        search.rewind_to_snapshot(snapshot0);

        assert!(history::tests::ops(&search.history).is_empty());
        assert!(state::tests::tc_seq(&search.state).is_empty());
    }

    /// Test that prune_leaf/suppress_node and undo_prune_leaf/undo_suppress_node are counterparts
    /// of each other
    #[test]
    fn do_undo_prune_leaf_suppress_node() {

        let (trees, newicks) = state::tests::build_forest();
        let mut search       = Search::new(trees, true, true);

        let d = Leaf::new(2);
        let e = Leaf::new(6);

        let newick0_0 = newicks[0].clone();
        let newick1_0 = newicks[1].clone();
        let newick2   = newicks[2].clone();
        let newick0_1 = String::from("((a,c),((b,f),((g,e),h)));");
        let newick0_2 = String::from("((a,c),((b,f),(g,h)));");
        let newick1_1 = String::from("((a,c),(((e,g),(h,f)),b));");
        let newick1_2 = String::from("((a,(c,d)),(((e,g),(h,f)),b));");

        let snapshot0 = search.history.take_snapshot();

        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick0_0.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick1_0.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick2.clone()));

        search.prune_leaf(d, 0);

        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick0_1.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick1_0.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick2.clone()));

        search.prune_leaf(e, 0);

        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick0_2.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick1_0.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick2.clone()));

        let snapshot1 = search.history.take_snapshot();

        search.prune_leaf(d, 1);

        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick0_2.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick1_1.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick2.clone()));

        search.rewind_to_snapshot(snapshot1);

        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick0_2.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick1_2.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick2.clone()));

        search.rewind_to_snapshot(snapshot0);

        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick0_0.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick1_2.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick2.clone()));
    }

    /// Test that remove_cherry and undo_remove_(trivial|non_trivial)_cherry are inverses
    #[test]
    fn do_undo_remove_cherry() {

        let (trees, _) = state::tests::build_forest();
        let mut search = Search::new(trees, true, true);
        let empty_vec: Vec<&cherry::Ref> = vec![];

        let snapshot0 = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.remove_cherry(cherry::Ref::Trivial(0));

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 0);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        let snapshot1 = search.history.take_snapshot();

        search.remove_cherry(cherry::Ref::NonTrivial(1));

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 0);
        assert_eq!(search.state.num_non_trivial_cherries(), 3);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot1);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 0);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot0);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);
    }

    /// Test that push/pop_trivial_cherry and undo_push/pop_trivial_cherry are inverses
    #[test]
    fn do_undo_push_pop_trivial_cherry() {

        let (trees, _) = state::tests::build_forest();
        let mut search = Search::new(trees, true, true);
        let empty_vec: Vec<&cherry::Ref> = vec![];

        let snapshot0 = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.push_trivial_cherry(cherry::Cherry::new(Leaf::new(3), Leaf::new(5), 0));

        let snapshot1 = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 2);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).indices(), (1, 1));
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.pop_trivial_cherry();

        let snapshot2 = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.pop_trivial_cherry();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 0);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot2);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot1);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 2);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).indices(), (1, 1));
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot0);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);
    }

    /// Test that record_cherry and undo_record_cherry are inverses
    #[test]
    fn do_undo_record_cherry() {

        let (trees, _) = state::tests::build_forest();
        let mut search = Search::new(trees, true, true);

        let snapshot0 = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.record_cherry(Leaf::new(4), Leaf::new(7), 0);

        let snapshot1 = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1, &0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.record_cherry(Leaf::new(4), Leaf::new(7), 2);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(1)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 2);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).indices(), (1, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&1, &0, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 3);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot1);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1, &0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);

        search.rewind_to_snapshot(snapshot0);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);
    }

    /// Test that resolve_trivial_cherries resolves trivial cherries correctly
    #[test]
    fn resolve_trivial_cherries() {

        let (trees, newicks) = state::tests::build_forest();
        let mut search       = Search::new(trees, true, true);

        let newick1          = String::from("(((a,c),d),((b,f),(e,h)));");
        let newick2          = String::from("((a,(d,c)),((e,(h,f)),b));");
        let newick3          = String::from("((((h,(f,(e,c))),b),a),d);");
        let newick1_restored = String::from("(((a,c),d),((b,f),((e,g),h)));");
        let newick3_restored = String::from("((((h,(f,((e,g),c))),b),a),d);");

        let empty_vec: Vec<&cherry::Ref> = vec![];

        let snapshot = search.history.take_snapshot();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newicks[0].clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newicks[1].clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newicks[2].clone()));

        search.resolve_trivial_cherries();

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3), &cherry::Ref::NonTrivial(5)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(4), &cherry::Ref::NonTrivial(5)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 0);
        assert_eq!(search.state.num_non_trivial_cherries(), 6);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 4).leaves(),
        (Leaf::new(6), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 4).indices(), (0, 1));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 4).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 5).leaves(),
        (Leaf::new(1), Leaf::new(6)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 5).indices(), (2, 1));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 5).trees().collect::<Vec<&usize>>(),
        vec![&2]);
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)), Some(newick1.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)), Some(newick2.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)), Some(newick3.clone()));

        search.rewind_to_snapshot(snapshot);

        assert_eq!(state::tests::leaf(&search.state, 0).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 1).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 2).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state::tests::leaf(&search.state, 3).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state::tests::leaf(&search.state, 4).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::leaf(&search.state, 5).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 6).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state::tests::leaf(&search.state, 7).cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state::tests::num_trivial_cherries(&search.state), 1);
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0, &1, &2]);
        assert_eq!(search.state.num_non_trivial_cherries(), 4);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).leaves(),
        (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 0).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).leaves(),
        (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).indices(), (0, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 1).trees().collect::<Vec<&usize>>(),
        vec![&0]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).leaves(),
        (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 2).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).leaves(),
        (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).indices(), (1, 0));
        assert_eq!(state::tests::non_trivial_cherry(&search.state, 3).trees().collect::<Vec<&usize>>(),
        vec![&1]);
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 0)),
        Some(newick1_restored.clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 1)),
        Some(newicks[1].clone()));
        assert_eq!(newick::format_tree(state::tests::tree(&search.state, 2)),
        Some(newick3_restored.clone()));
    }
}
