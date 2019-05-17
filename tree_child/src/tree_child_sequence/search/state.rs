//! This module implements the ephemeral part of the search state.  No history is recorded.

use std::cmp::min;
use std::mem;
use super::cherry;
use super::leaf;
use super::super::{Pair, TcSeq};
use tree::{Tree, Leaf, Node};

/// The state of the search for a tree-child sequence
#[derive(Clone)]
pub struct State<T> {

    /// The trees for which to find a TC sequence
    pub trees: Vec<Tree<T>>,

    /// The number of leaves that have not been pruned from all trees yet
    num_leaves: usize,

    /// The information associated with the leaves during the search
    leaves: Vec<leaf::Leaf>,

    /// The list of trivial cherries
    trivial_cherries: Vec<cherry::Cherry>,

    /// The list of non-trivial cherries
    non_trivial_cherries: Vec<cherry::Cherry>,

    /// The maximum allowed weight of the constructed sequence.  (This is the parameter "k" in the
    /// FPT formulation of the algorithm.)
    max_weight: usize,

    /// The weight of the current tree-child sequence
    weight: usize,

    /// The currently constructed tree-child sequence
    tc_seq: TcSeq<Leaf>,
}

impl<T: Clone> State<T> {

    //----------------------------------------------------------------------------------------------
    // Initialization code
    //----------------------------------------------------------------------------------------------

    /// Create a new search state for a given set of trees
    pub fn new(trees: Vec<Tree<T>>) -> Self {

        let num_leaves = trees[0].leaf_count();
        let leaves     = vec![leaf::Leaf::new(trees.len()); num_leaves];

        let mut state = Self {
            trees,
            num_leaves,
            leaves,
            trivial_cherries:     vec![],
            non_trivial_cherries: vec![],
            max_weight:           0,
            weight:               0,
            tc_seq:               vec![],
        };

        state.find_cherries();
        state
    }

    /// Find all cherries in a set of trees
    fn find_cherries(&mut self) {

        let mut cherries = vec![];

        for (i, tree) in self.trees.iter().enumerate() {
            for u in tree.leaves() {
                if let (Some(u), Some(p)) = (tree.leaf_id(u), tree.parent(u)) {
                    for v in tree.children(p) {
                        if let Some(v) = tree.leaf_id(v) {
                            if u < v {
                                cherries.push((u, v, i));
                            }
                        }
                    }
                }
            }
        }

        for (u, v, tree) in cherries {
            self.record_cherry(u, v, tree);
        }
    }

    //----------------------------------------------------------------------------------------------
    // Increase the parameter for the current search
    //----------------------------------------------------------------------------------------------

    /// Increase the parameter of the search
    pub fn increase_max_weight(&mut self) -> bool {
        self.max_weight += 1;
        self.max_weight < self.leaves.len()
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the lists of cherries
    //----------------------------------------------------------------------------------------------

    /// Record a cherry (u, v) occurring in the given tree.  The return value is a reference to the
    /// recorded cherry.  The recorded cherry is always added to the list of non-trivial cherries
    /// first.  If it turns out to be a trivial cherry now, it is moved to the list of non-trivial
    /// cherries.  In this case, the second part of the return value is a reference to the original
    /// position of the cherry in the list of non-trivial cherries, in order to be able to restore
    /// the cherry to this position when undoing the operation.
    pub fn record_cherry(
        &mut self,
        u:    Leaf,
        v:    Leaf,
        tree: usize) -> (cherry::Ref, Option<cherry::Ref>) {

        // See whether we already have a cherry (u, v) on record
        let cherry_ref = self.leaf(u).cherries()

            .find(|&&cherry_ref| {
                let (x, y) = self.cherry(cherry_ref).leaves();
                x == v || y == v
            })

            .map(|&cherry_ref| cherry_ref);

        // Add the current tree to the list of trees for this cherry or create a new cherry
        let cherry_ref = if let Some(cherry_ref) = cherry_ref {
            self.cherry_mut(cherry_ref).push_tree(tree);
            cherry_ref
        } else {
            self.push_non_trivial_cherry(cherry::Cherry::new(u, v, tree))
        };

        let num_cherry_occurrences = self.cherry(cherry_ref).num_occurrences();
        let num_leaf_occurrences = min(
            self.leaf(u).num_occurrences(),
            self.leaf(v).num_occurrences());

        // Mark the cherry as trivial if adding the new occurrence made it trivial
        if num_leaf_occurrences == num_cherry_occurrences {
            let cherry = self.remove_cherry(cherry_ref);
            (self.push_trivial_cherry(cherry), Some(cherry_ref))
        } else {
            (cherry_ref, None)
        }
    }

    /// Forget a cherry that was previously recorded
    pub fn forget_cherry(&mut self, forget: cherry::Ref, restore: Option<cherry::Ref>) {

        // Forget the last tree
        self.cherry_mut(forget).pop_tree();

        if self.cherry(forget).num_occurrences() == 0 {

            // Completely remove the cherry if it no longer occurs in any tree
            self.remove_cherry(forget);

        } else if let Some(restore) = restore {

            // If the cherry was moved from the list of non-trivial cherries to the list of trivial
            // cherries when recording it, it needs to be moved back now.
            let cherry = self.remove_cherry(forget);
            self.restore_cherry(restore, cherry);
        }
    }

    /// Check whether the given leaf is part of a trivial cherry
    pub fn check_for_trivial_cherry(&self, leaf: Leaf) -> Option<cherry::Ref> {

        let leaf = self.leaf(leaf);

        // The leaf can be part of a trivial cherry only if there is exactly one cherry involving
        // this leaf.
        if leaf.num_cherries() == 1 {

            let cherry_ref = leaf.cherry(0);

            // It *is* part of a trivial cherry if the leaf occurs exactly as often as the cherry
            // it is part of.
            if leaf.num_occurrences() == self.cherry(cherry_ref).num_occurrences() {
                return Some(cherry_ref);
            }
        }

        None
    }

    /// Check whether the given node forms a cherry in the given tree
    pub fn check_for_cherry(&self, node: Node, tree: usize) -> Option<(Leaf, Leaf)> {

        let tree = self.tree(tree);

        // To be part of a cherry, the node must be a leaf and have a parent
        if let (Some(leaf), Some(parent)) = (tree.leaf_id(node), tree.parent(node)) {

            for sib in tree.children(parent) {
                if sib != node {

                    // If the sibling is a leaf, we have a cherry
                    if let Some(sib) = tree.leaf_id(sib) {

                        // Order it smallest leaf first
                        return Some(if leaf < sib {
                            (leaf, sib)
                        } else  {
                            (sib, leaf)
                        })
                    }
                }
            }
        }

        None
    }

    /// Push a cherry to the end of the list of trivial cherries
    pub fn push_trivial_cherry(&mut self, mut cherry: cherry::Cherry) -> cherry::Ref {

        let cherry_ref = cherry::Ref::Trivial(self.trivial_cherries.len());
        let (u, v)     = cherry.leaves();
        let uix        = self.leaf(u).num_cherries();
        let vix        = self.leaf(v).num_cherries();

        cherry.set_indices(uix, vix);
        self.leaf_mut(u).add_cherry(cherry_ref);
        self.leaf_mut(v).add_cherry(cherry_ref);
        self.trivial_cherries.push(cherry);

        cherry_ref
    }

    /// Push a cherry to the end of the list of non-trivial cherries
    pub fn push_non_trivial_cherry(&mut self, mut cherry: cherry::Cherry) -> cherry::Ref {

        let cherry_ref = cherry::Ref::NonTrivial(self.non_trivial_cherries.len());
        let (u, v)     = cherry.leaves();
        let uix        = self.leaf(u).num_cherries();
        let vix        = self.leaf(v).num_cherries();

        cherry.set_indices(uix, vix);
        self.leaf_mut(u).add_cherry(cherry_ref);
        self.leaf_mut(v).add_cherry(cherry_ref);
        self.non_trivial_cherries.push(cherry);

        cherry_ref
    }

    /// Pop a trivial cherry from the end of the list of non-trivial cherries
    pub fn pop_trivial_cherry(&mut self) -> Option<cherry::Cherry> {

        self.trivial_cherries.pop().map(|cherry| {

            let (u, v)     = cherry.leaves();
            let (uix, vix) = cherry.indices();

            self.remove_cherry_ref(u, uix);
            self.remove_cherry_ref(v, vix);

            cherry
        })
    }

    /// Remove a cherry from the middle of the list of trivial or non-trivial cherries
    pub fn remove_cherry(&mut self, cherry_ref: cherry::Ref) -> cherry::Cherry {

        // Helper to remove a cherry from a given cherry list
        fn remove_from_cherry_list(cherries: &mut Vec<cherry::Cherry>, ix: usize)
            -> (cherry::Cherry, Option<&cherry::Cherry>) {

            let cherry      = cherries.swap_remove(ix);
            let replacement = if ix < cherries.len() {
                Some(&cherries[ix])
            } else {
                None
            };
            (cherry, replacement)
        }

        // First remove the cherry from the list of cherries
        let (cherry, updates) = {
            
            let (cherry, replacement) = match cherry_ref {

                cherry::Ref::Trivial(ix) =>
                    remove_from_cherry_list(&mut self.trivial_cherries, ix),

                cherry::Ref::NonTrivial(ix) =>
                    remove_from_cherry_list(&mut self.non_trivial_cherries, ix),
            };

            (cherry, replacement.map(|replacement| (replacement.leaves(), replacement.indices())))
        };

        // Since we do this by moving a different cherry in its place, we need to update the
        // references to this moved cherry.
        if let Some(((u, v), (uix, vix))) = updates {
            self.leaf_mut(u).replace_cherry(uix, cherry_ref);
            self.leaf_mut(v).replace_cherry(vix, cherry_ref);
        }

        // Now remove all references to the removed cherry
        let (u, v)     = cherry.leaves();
        let (uix, vix) = cherry.indices();
        self.remove_cherry_ref(u, uix);
        self.remove_cherry_ref(v, vix);

        cherry
    }

    /// Restore a cherry to its original position in one of the two cherry lists
    pub fn restore_cherry(&mut self, cherry_ref: cherry::Ref, mut cherry: cherry::Cherry) {

        // Restore references to the cherry to be restored
        let (u, v)     = cherry.leaves();
        let (uix, vix) = cherry.indices();
        self.restore_cherry_ref(u, uix, cherry_ref);
        self.restore_cherry_ref(v, vix, cherry_ref);

        let (updates, ref_to_end) = {

            let (cherries, ix, ref_to_end) = match cherry_ref {

                cherry::Ref::Trivial(ix) => {
                    let num_cherries = self.trivial_cherries.len();
                    let ref_to_end   = cherry::Ref::Trivial(num_cherries);
                    (&mut self.trivial_cherries, ix, ref_to_end)
                },

                cherry::Ref::NonTrivial(ix) => {
                    let num_cherries = self.non_trivial_cherries.len();
                    let ref_to_end   = cherry::Ref::NonTrivial(num_cherries);
                    (&mut self.non_trivial_cherries, ix, ref_to_end)
                },
            };

            let updates = if cherry_ref < ref_to_end {
                mem::swap(&mut cherries[ix], &mut cherry);
                Some((cherry.leaves(), cherry.indices()))
            } else {
                None
            };
            cherries.push(cherry);

            (updates, ref_to_end)
        };

        if let Some(((x, y), (xix, yix))) = updates {
            self.leaf_mut(x).replace_cherry(xix, ref_to_end);
            self.leaf_mut(y).replace_cherry(yix, ref_to_end);
        }
    }

    /// Remove the `index`th cherry reference associated with `leaf`
    fn remove_cherry_ref(&mut self, leaf: Leaf, index: usize) {

        self.leaf_mut(leaf).remove_cherry(index);

        if index < self.leaf(leaf).num_cherries() {
            let cherry_ref = self.leaf(leaf).cherry(index);
            self.cherry_mut(cherry_ref).set_index(leaf, index);
        }
    }

    /// Restore the `index`th cherry reference associated with `leaf`
    fn restore_cherry_ref(&mut self, leaf: Leaf, index: usize, mut cherry_ref: cherry::Ref) {

        let num_cherries = self.leaf(leaf).num_cherries();

        if index < num_cherries {
            mem::swap(&mut cherry_ref, self.leaf_mut(leaf).cherry_mut(index));
            self.cherry_mut(cherry_ref).set_index(leaf, num_cherries);
        }

        self.leaf_mut(leaf).add_cherry(cherry_ref);
    }

    /// Record the cutting of a leaf from a cherry
    pub fn cut(&mut self, cherry_ref: cherry::Ref, first_leaf: bool) -> usize {
        let cherry    = self.cherry_mut(cherry_ref);
        let cut_count = cherry.cut_count(first_leaf);
        cherry.cut(first_leaf);
        cut_count
    }

    /// Reset the cut counts of all non-trivial cherries that contain w
    pub fn reset_cut_counts(&mut self, w: Leaf) -> Option<Vec<(cherry::Ref, bool, usize)>> {
        let mut reset_cherries = vec![];
        for (ix, cherry) in self.non_trivial_cherries.iter_mut().enumerate() {
            if let Some((first_leaf, old_count)) = cherry.reset_cut_count(w) {
                reset_cherries.push((cherry::Ref::NonTrivial(ix), first_leaf, old_count));
            }
        }
        if reset_cherries.len() == 0 {
            None
        } else {
            Some(reset_cherries)
        }
    }

    /// Restore the cut count of a leaf in a cherry
    pub fn restore_cut_count(&mut self, cherry_ref: cherry::Ref, first_leaf: bool, cut_count: usize) {
        let cherry = self.cherry_mut(cherry_ref);
        cherry.set_cut_count(first_leaf, cut_count);
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the trees
    //----------------------------------------------------------------------------------------------

    /// Prune a leaf from a tree
    pub fn prune_leaf(&mut self, leaf: Leaf, tree: usize) -> Option<Node> {

        self.leaf_mut(leaf).decrease_num_occurrences();

        if self.leaf(leaf).num_occurrences() == 0 {
            self.num_leaves -= 1;
        }

        self.tree_mut(tree).prune_leaf(leaf)
    }

    /// Restore a leaf that was previously pruned
    pub fn restore_leaf(&mut self, leaf: Leaf, tree: usize) {

        if self.leaf(leaf).num_occurrences() == 0 {
            self.num_leaves += 1;
        }

        self.leaf_mut(leaf).increase_num_occurrences();
        self.tree_mut(tree).restore_leaf(leaf);
    }

    /// Suppress an internal node
    pub fn suppress_node(&mut self, node: Node, tree: usize) -> Node {
        self.tree_mut(tree).suppress_node(node)
    }

    /// Restore an internal node
    pub fn restore_node(&mut self, node: Node, tree: usize) {
        self.tree_mut(tree).restore_node(node)
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the tree-chlid sequence
    //----------------------------------------------------------------------------------------------

    /// Push a trivial pair to the end of the tree-child sequence
    pub fn push_trivial_tree_child_pair(&mut self, u: Leaf, v: Leaf) {
        self.tc_seq.push(Pair::Trivial(u, v));
        self.leaf_mut(u).increase_times_pruned();
    }

    /// Push a non-trivial pair to the end of the tree-child sequence
    pub fn push_non_trivial_tree_child_pair(&mut self, u: Leaf, v: Leaf) {
        self.tc_seq.push(Pair::NonTrivial(u, v));
        self.leaf_mut(u).increase_times_pruned();
    }

    /// Push the final pair in the tree-child sequence
    pub fn push_final_tree_child_pair(&mut self, leaf: Leaf) {
        self.tc_seq.push(Pair::Final(leaf));
        self.leaf_mut(leaf).increase_times_pruned();
    }

    /// Remove the last pair form the tree-child sequence
    pub fn pop_tree_child_pair(&mut self) {
        let leaf = match self.tc_seq.pop().unwrap() {
            Pair::Trivial(u, _) => u,
            Pair::NonTrivial(u, _) => u,
            Pair::Final(leaf) => leaf,
        };
        self.leaf_mut(leaf).decrease_times_pruned();
    }

    /// Retrieve the tree-child sequence
    pub fn tc_seq(self) -> TcSeq<T> {

        let labels = self.tree(0).labels();

        self.tc_seq.into_iter()
            .map(|pair| {
                match pair {

                    Pair::Trivial(u, v) =>
                        Pair::Trivial(labels[u.id()].clone(), labels[v.id()].clone()),

                    Pair::NonTrivial(u, v) =>
                        Pair::NonTrivial(labels[u.id()].clone(), labels[v.id()].clone()),

                    Pair::Final(u) =>
                        Pair::Final(labels[u.id()].clone()),
                }
            })
            .collect()
    }

    //----------------------------------------------------------------------------------------------
    // Access primitives to cherries, trees, and leaf data
    //----------------------------------------------------------------------------------------------

    /// Get a reference to a cherry
    fn cherry(&self, cherry_ref: cherry::Ref) -> &cherry::Cherry {
        match cherry_ref {
            cherry::Ref::Trivial(index)    => &self.trivial_cherries[index],
            cherry::Ref::NonTrivial(index) => &self.non_trivial_cherries[index],
        }
    }

    /// Get a mutable reference to a cherry
    fn cherry_mut(&mut self, cherry_ref: cherry::Ref) -> &mut cherry::Cherry {
        match cherry_ref {
            cherry::Ref::Trivial(index)    => &mut self.trivial_cherries[index],
            cherry::Ref::NonTrivial(index) => &mut self.non_trivial_cherries[index],
        }
    }

    /// Get a reference to a given tree
    fn tree(&self, tree: usize) -> &Tree<T> {
        &self.trees[tree]
    }

    /// Get a mutable reference to a given tree
    fn tree_mut(&mut self, tree: usize) -> &mut Tree<T> {
        &mut self.trees[tree]
    }

    /// Get a reference to the data for the given leaf
    pub fn leaf(&self, leaf: Leaf)-> &leaf::Leaf {
        &self.leaves[leaf.id()]
    }

    /// Get a mutable reference to the data for the given leaf
    fn leaf_mut(&mut self, leaf: Leaf)-> &mut leaf::Leaf {
        &mut self.leaves[leaf.id()]
    }

    //----------------------------------------------------------------------------------------------
    // Basic stats
    //----------------------------------------------------------------------------------------------

    /// The final leaf that is still alive if there is only one, otherwise None.
    pub fn final_leaf(&self) -> Option<Leaf> {
        if self.num_leaves == 1 {
            for (i, leaf) in self.leaves.iter().enumerate() {
                if leaf.num_occurrences() > 0 {
                    return Some(Leaf::new(i));
                }
            }
        }
        None
    }

    /// The number of trees
    pub fn num_trees(&self) -> usize {
        self.trees.len()
    }

    /// The number of non-trivial cherries
    pub fn num_non_trivial_cherries(&self) -> usize {
        self.non_trivial_cherries.len()
    }

    /// Increase the weight of the current sequence
    pub fn increase_weight(&mut self) {
        self.weight += 1;
    }

    /// Decrease the weight of the current sequence
    pub fn decrease_weight(&mut self) {
        self.weight -= 1;
    }

    /// The weight of the sequence so far (the number of non-trivial cherries resolve)
    pub fn weight(&self) -> usize {
        self.weight
    }

    /// The maximum weight of the sequence in the current search
    pub fn max_weight(&self) -> usize {
        self.max_weight
    }
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use newick;
    use tree::TreeBuilder;

    /// Construct a forest to be used in subsequent tests
    pub fn build_forest() -> (Vec<Tree<String>>, Vec<String>) {

        let mut builder  = TreeBuilder::<String>::new();

        let tree1_newick = String::from("(((a,c),d),((b,f),((g,e),h)));");
        let tree2_newick = String::from("((a,(d,c)),(((e,g),(h,f)),b));");
        let tree3_newick = String::from("((((h,(f,((g,e),c))),b),a),d);");
        let mut newick   = String::new();
        newick += &tree1_newick;
        newick.push('\n');
        newick += &tree2_newick;
        newick.push('\n');
        newick += &tree3_newick;
        newick.push('\n');

        newick::parse_forest(&mut builder, &newick).unwrap();
        (builder.trees(), vec![tree1_newick, tree2_newick, tree3_newick])
    }

    /// Test that new initializes the state correctly.  This is mainly just a sanity check.
    #[test]
    fn new() {
        let (trees, newicks) = build_forest();
        let state = State::new(trees);
        test_new(state, newicks);
    }

    /// The actual test of the initial state (in a separate method for reuse in the search
    /// tests).
    pub fn test_new(state: State<String>, newicks: Vec<String>) {

        // We need to have the right number of trees and they need to be unaltered from the input.
        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(newicks[0].clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(newicks[1].clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(newicks[2].clone()));

        // There are 8 leaves, which occur in each tree.
        assert_eq!(state.num_leaves, 8);
        for leaf in &state.leaves {
            assert_eq!(leaf.num_occurrences(), 3);
        }

        // Check the list of references to cherries stored for each leaf
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);

        // Check the list of trivial cherries
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);

        // Check the list of non-trivial cherries
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // Weights should be 0 and the sequence should be empty
        assert_eq!(state.max_weight, 0);
        assert_eq!(state.weight, 0);
        assert_eq!(state.tc_seq().len(), 0);
    }

    /// Test that increase_max_weight increases the maximum weight and max_weight reports the
    /// current max weight
    #[test]
    fn increase_query_max_weight() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        assert_eq!(state.max_weight(), 0);

        state.increase_max_weight();

        assert_eq!(state.max_weight(), 1);

        state.increase_max_weight();

        assert_eq!(state.max_weight(), 2);
    }

    /// Test that increase_weight/decrease_weight are inverses of each other and weight reports the
    /// correct weight
    #[test]
    fn increase_decrease_query_weight() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        assert_eq!(state.weight(), 0);

        state.increase_weight();

        assert_eq!(state.weight(), 1);

        state.increase_weight();

        assert_eq!(state.weight(), 2);

        state.decrease_weight();

        assert_eq!(state.weight(), 1);

        state.increase_weight();

        assert_eq!(state.weight(), 2);

        state.decrease_weight();

        assert_eq!(state.weight(), 1);

        state.decrease_weight();

        assert_eq!(state.weight(), 0);
    }

    /// Test that record_cherry/forget_cherry manipulate the list of cherries
    /// correctly
    #[test]
    fn record_and_forget_cherry() {
        // TODO: This does not currently test that cherries are classified correctly as trivial or
        // non-trivial once not all leaves occur in all trees.

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        // Record two new fictional cherries
        let (rec1, mov1) = state.record_cherry(Leaf::new(1), Leaf::new(2), 0);
        let (rec2, mov2) = state.record_cherry(Leaf::new(3), Leaf::new(7), 2);

        // Check that references to them occur in the cherry lists of the affected leaves
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::NonTrivial(4)]);

        // Check that they are added to the list of non-trivial cherries
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 5);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1, &0]);
        assert_eq!(state.non_trivial_cherries[4].leaves(), (Leaf::new(3), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[4].indices(), (1, 1));
        assert_eq!(state.non_trivial_cherries[4].trees().collect::<Vec<&usize>>(), vec![&2]);

        // Recording cherry (1, 2) once more should make it trivial now because it occurs in all
        // trees
        let (rec3, mov3) = state.record_cherry(Leaf::new(1), Leaf::new(2), 2);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.trivial_cherries.len(), 2);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 0));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&1, &0, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(3), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 1));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&2]);

        // Forgetting cherry (1, 2) should get us back to the previous state
        state.forget_cherry(rec3, mov3);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 5);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1, &0]);
        assert_eq!(state.non_trivial_cherries[4].leaves(), (Leaf::new(3), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[4].indices(), (1, 1));
        assert_eq!(state.non_trivial_cherries[4].trees().collect::<Vec<&usize>>(), vec![&2]);

        // Forget (3, 7)
        state.forget_cherry(rec2, mov2);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1, &0]);

        // Forget (1, 2); we should be back to the original state now
        state.forget_cherry(rec1, mov1);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);
    }

    /// Check that check_for_trivial_cherry identifies a trivial cherry correctly.
    #[test]
    fn check_for_trivial_cherry() {
        // TODO: This does not test that check_for_trivial_cherries works when not every leaf
        // occurs the same number of times

        let (trees, _) = build_forest();
        let state = State::new(trees);

        assert_eq!(state.check_for_trivial_cherry(Leaf::new(0)), None);
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(1)), None);
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(2)), None);
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(3)), None);
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(4)), None);
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(5)), Some(cherry::Ref::Trivial(0)));
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(6)), Some(cherry::Ref::Trivial(0)));
        assert_eq!(state.check_for_trivial_cherry(Leaf::new(7)), None);
    }

    /// Check that check_for_cherry finds all cherries
    #[test]
    fn check_for_cherry() {

        let (trees, _) = build_forest();
        let state = State::new(trees);

        assert_eq!(state.check_for_cherry(Node::new(0), 0), Some((Leaf::new(0), Leaf::new(1))));
        assert_eq!(state.check_for_cherry(Node::new(1), 0), Some((Leaf::new(0), Leaf::new(1))));
        assert_eq!(state.check_for_cherry(Node::new(2), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(3), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(4), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(5), 0), Some((Leaf::new(3), Leaf::new(4))));
        assert_eq!(state.check_for_cherry(Node::new(6), 0), Some((Leaf::new(3), Leaf::new(4))));
        assert_eq!(state.check_for_cherry(Node::new(7), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(8), 0), Some((Leaf::new(5), Leaf::new(6))));
        assert_eq!(state.check_for_cherry(Node::new(9), 0), Some((Leaf::new(5), Leaf::new(6))));
        assert_eq!(state.check_for_cherry(Node::new(10), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(11), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(12), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(13), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(14), 0), None);
        assert_eq!(state.check_for_cherry(Node::new(0), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(1), 1), Some((Leaf::new(1), Leaf::new(2))));
        assert_eq!(state.check_for_cherry(Node::new(2), 1), Some((Leaf::new(1), Leaf::new(2))));
        assert_eq!(state.check_for_cherry(Node::new(3), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(4), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(5), 1), Some((Leaf::new(5), Leaf::new(6))));
        assert_eq!(state.check_for_cherry(Node::new(6), 1), Some((Leaf::new(5), Leaf::new(6))));
        assert_eq!(state.check_for_cherry(Node::new(7), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(8), 1), Some((Leaf::new(4), Leaf::new(7))));
        assert_eq!(state.check_for_cherry(Node::new(9), 1), Some((Leaf::new(4), Leaf::new(7))));
        assert_eq!(state.check_for_cherry(Node::new(10), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(11), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(12), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(13), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(14), 1), None);
        assert_eq!(state.check_for_cherry(Node::new(0), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(1), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(2), 2), Some((Leaf::new(5), Leaf::new(6))));
        assert_eq!(state.check_for_cherry(Node::new(3), 2), Some((Leaf::new(5), Leaf::new(6))));
        assert_eq!(state.check_for_cherry(Node::new(4), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(5), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(6), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(7), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(8), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(9), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(10), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(11), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(12), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(13), 2), None);
        assert_eq!(state.check_for_cherry(Node::new(14), 2), None);
    }

    /// Test that push_trivial_cherry/pop_trivial_cherry manipulate the list of trivial cherries
    /// correctly, including maintainance of references from leaf records into the cherry lists.
    #[test]
    pub fn push_pop_trivial_cherry() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        // Push a trivial cherry (3, 5)
        let cherry_ref =
            state.push_trivial_cherry(cherry::Cherry::new(Leaf::new(3), Leaf::new(5), 3));

        assert_eq!(cherry_ref, cherry::Ref::Trivial(1));
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 2);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Push a trivial cherry (2, 7)
        let cherry_ref =
            state.push_trivial_cherry(cherry::Cherry::new(Leaf::new(2), Leaf::new(7), 3));

        assert_eq!(cherry_ref, cherry::Ref::Trivial(2));
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3), &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::Trivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 3);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.trivial_cherries[2].leaves(), (Leaf::new(2), Leaf::new(7)));
        assert_eq!(state.trivial_cherries[2].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Pop the cherry (2, 7) again
        let cherry = &state.pop_trivial_cherry();

        assert_eq!(cherry.as_ref().unwrap().leaves(), (Leaf::new(2), Leaf::new(7)));
        assert_eq!(cherry.as_ref().unwrap().trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 2);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Push (1, 4)
        let cherry_ref =
            state.push_trivial_cherry(cherry::Cherry::new(Leaf::new(1), Leaf::new(4), 3));

        assert_eq!(cherry_ref, cherry::Ref::Trivial(2));
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3),
                   &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2),
                   &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 3);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.trivial_cherries[2].leaves(), (Leaf::new(1), Leaf::new(4)));
        assert_eq!(state.trivial_cherries[2].indices(), (2, 2));
        assert_eq!(state.trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Push (2, 7)
        let cherry_ref =
            state.push_trivial_cherry(cherry::Cherry::new(Leaf::new(2), Leaf::new(7), 3));

        assert_eq!(cherry_ref, cherry::Ref::Trivial(3));
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3),
                   &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3), &cherry::Ref::Trivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2),
                   &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::Trivial(3)]);
        assert_eq!(state.trivial_cherries.len(), 4);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.trivial_cherries[2].leaves(), (Leaf::new(1), Leaf::new(4)));
        assert_eq!(state.trivial_cherries[2].indices(), (2, 2));
        assert_eq!(state.trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.trivial_cherries[3].leaves(), (Leaf::new(2), Leaf::new(7)));
        assert_eq!(state.trivial_cherries[3].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Pop (2, 7)
        let cherry = &state.pop_trivial_cherry();

        assert_eq!(cherry.as_ref().unwrap().leaves(), (Leaf::new(2), Leaf::new(7)));
        assert_eq!(cherry.as_ref().unwrap().trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3),
                   &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2),
                   &cherry::Ref::Trivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 3);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.trivial_cherries[2].leaves(), (Leaf::new(1), Leaf::new(4)));
        assert_eq!(state.trivial_cherries[2].indices(), (2, 2));
        assert_eq!(state.trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Pop (1, 4)
        let cherry = &state.pop_trivial_cherry();

        assert_eq!(cherry.as_ref().unwrap().leaves(), (Leaf::new(1), Leaf::new(4)));
        assert_eq!(cherry.as_ref().unwrap().trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 2);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.trivial_cherries[1].indices(), (1, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Pop (3, 5)
        let cherry = &state.pop_trivial_cherry();

        assert_eq!(cherry.as_ref().unwrap().leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(cherry.as_ref().unwrap().trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
    }

    /// Test that push_non_trivial_cherry manipulates the list of non-trivial cherries correctly,
    /// including references from leaf records into the cherry list.  There is no inverse
    /// pop_non_trivial_cherry operation because it's not needed by the algorithm.
    #[test]
    pub fn push_non_trivial_cherry() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        // Push (3, 5)
        let cherry_ref =
            state.push_non_trivial_cherry(cherry::Cherry::new(Leaf::new(3), Leaf::new(5), 3));

        assert_eq!(cherry_ref, cherry::Ref::NonTrivial(4));
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.non_trivial_cherries.len(), 5);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[4].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.non_trivial_cherries[4].indices(), (1, 1));
        assert_eq!(state.non_trivial_cherries[4].trees().collect::<Vec<&usize>>(), vec![&3]);

        // Push (2, 7)
        let cherry_ref =
            state.push_non_trivial_cherry(cherry::Cherry::new(Leaf::new(2), Leaf::new(7), 3));

        assert_eq!(cherry_ref, cherry::Ref::NonTrivial(5));
        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3), &cherry::Ref::NonTrivial(5)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0), &cherry::Ref::NonTrivial(4)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2), &cherry::Ref::NonTrivial(5)]);
        assert_eq!(state.non_trivial_cherries.len(), 6);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[4].leaves(), (Leaf::new(3), Leaf::new(5)));
        assert_eq!(state.non_trivial_cherries[4].indices(), (1, 1));
        assert_eq!(state.non_trivial_cherries[4].trees().collect::<Vec<&usize>>(), vec![&3]);
        assert_eq!(state.non_trivial_cherries[5].leaves(), (Leaf::new(2), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[5].indices(), (1, 1));
        assert_eq!(state.non_trivial_cherries[5].trees().collect::<Vec<&usize>>(), vec![&3]);
    }

    /// Test the correct behaviour of remove_cherry, restore_trivial_cherry, and
    /// restore_non_trivial_cherry
    #[test]
    fn remove_restore_trivial_non_trivial_cherry() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        // Remove the last non-trivial cherry
        let cherry_ref = cherry::Ref::NonTrivial(3);
        let cherry     = state.remove_cherry(cherry_ref);
        let empty_vec: Vec<&cherry::Ref> = vec![];

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 3);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and restore it.
        state.restore_cherry(cherry_ref, cherry);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // Remove a non-trivial cherry from the middle
        let cherry_ref = cherry::Ref::NonTrivial(1);
        let cherry     = state.remove_cherry(cherry_ref);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 3);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and restore it.
        state.restore_cherry(cherry_ref, cherry);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // Remove the last trivial cherry
        let cherry_ref = cherry::Ref::Trivial(0);
        let cherry     = state.remove_cherry(cherry_ref);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 0);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and restore it.
        state.restore_cherry(cherry_ref, cherry);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // Remove a trivial cherry from the middle
        state.push_trivial_cherry(cherry::Cherry::new(Leaf::new(1), Leaf::new(2), 0));
        let cherry_ref = cherry::Ref::Trivial(0);
        let cherry     = state.remove_cherry(cherry_ref);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3),
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3), &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.trivial_cherries[0].indices(), (2, 1));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and restore it.
        state.restore_cherry(cherry_ref, cherry);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3),
                   &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3), &cherry::Ref::Trivial(1)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 2);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.trivial_cherries[1].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.trivial_cherries[1].indices(), (2, 1));
        assert_eq!(state.trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);
    }

    /// Check that remove_cherry_ref and restore_cherry_ref correctly manipulate the list of
    /// references from leaf records to cherries.
    #[test]
    fn remove_restore_cherry_ref() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        // Get rid of leaf 1's 0th cherry (not the last cherry in the list, so the old last
        // cherry's cross pointers must be updated).
        state.remove_cherry_ref(Leaf::new(1), 0);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and bring it back (the old last cherry is back in the last place and again has the
        // correct cross pointers).
        state.restore_cherry_ref(Leaf::new(1), 0, cherry::Ref::NonTrivial(0));

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // Remove the last cherry of leaf 4.
        state.remove_cherry_ref(Leaf::new(4), 1);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and restore it.
        state.restore_cherry_ref(Leaf::new(4), 1, cherry::Ref::NonTrivial(2));

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // Remove the only cherry of leaf 5.
        let empty_vec: Vec<&cherry::Ref> = vec![];
        state.remove_cherry_ref(Leaf::new(5), 0);

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), empty_vec);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);

        // ... and restore it.
        state.restore_cherry_ref(Leaf::new(5), 0, cherry::Ref::Trivial(0));

        assert_eq!(state.leaves[0].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0)]);
        assert_eq!(state.leaves[1].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(0), &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[2].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(3)]);
        assert_eq!(state.leaves[3].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1)]);
        assert_eq!(state.leaves[4].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(1), &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.leaves[5].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[6].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::Trivial(0)]);
        assert_eq!(state.leaves[7].cherries().collect::<Vec<&cherry::Ref>>(), vec![
                   &cherry::Ref::NonTrivial(2)]);
        assert_eq!(state.trivial_cherries.len(), 1);
        assert_eq!(state.trivial_cherries[0].leaves(), (Leaf::new(5), Leaf::new(6)));
        assert_eq!(state.trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0, &1, &2]);
        assert_eq!(state.num_non_trivial_cherries(), 4);
        assert_eq!(state.non_trivial_cherries[0].leaves(), (Leaf::new(0), Leaf::new(1)));
        assert_eq!(state.non_trivial_cherries[0].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[0].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[1].leaves(), (Leaf::new(3), Leaf::new(4)));
        assert_eq!(state.non_trivial_cherries[1].indices(), (0, 0));
        assert_eq!(state.non_trivial_cherries[1].trees().collect::<Vec<&usize>>(), vec![&0]);
        assert_eq!(state.non_trivial_cherries[2].leaves(), (Leaf::new(4), Leaf::new(7)));
        assert_eq!(state.non_trivial_cherries[2].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[2].trees().collect::<Vec<&usize>>(), vec![&1]);
        assert_eq!(state.non_trivial_cherries[3].leaves(), (Leaf::new(1), Leaf::new(2)));
        assert_eq!(state.non_trivial_cherries[3].indices(), (1, 0));
        assert_eq!(state.non_trivial_cherries[3].trees().collect::<Vec<&usize>>(), vec![&1]);
    }

    /// Check that prune_leaf and restore_leaf correctly prune and restore leaves and update the
    /// number of occurrences of the affected leaf correctly.
    #[test]
    fn prune_restore_leaf() {
        // The Newick strings of the trees expected to result from the prune/restore operations.
        // Restore operations do not ensure that a leaf is attached in the same position of the
        // parent's child list, so the restored Newick strings may be different from the strings
        // before the prune operation.
        let tree1_newick_pruned = String::from("(((a,c),d),((b),((g,e),h)));");
        let tree2_newick_pruned = String::from("((a,(d,c)),(((e,g),(h)),b));");
        let tree3_newick_pruned = String::from("((((h,(((g,e),c))),b),a),d);");
        let tree1_newick_restored = String::from("(((a,c),d),((b,f),((g,e),h)));");
        let tree2_newick_restored = String::from("((a,(d,c)),(((e,g),(h,f)),b));");
        let tree3_newick_restored = String::from("((((h,(((g,e),c),f)),b),a),d);");

        let (trees, newicks) = build_forest();
        let mut state = State::new(trees);

        // Prune leaf 4; it now occurs only twice.
        state.prune_leaf(Leaf::new(4), 1);

        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(newicks[0].clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(newicks[2].clone()));
        assert_eq!(state.num_leaves, 8);
        for (i, leaf) in state.leaves.iter().enumerate() {
            if i == 4 {
                assert_eq!(leaf.num_occurrences(), 2);
            } else {
                assert_eq!(leaf.num_occurrences(), 3);
            }
        }

        // Prune it from tree 2; it now occurs only once.
        state.prune_leaf(Leaf::new(4), 2);

        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(newicks[0].clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_pruned.clone()));
        assert_eq!(state.num_leaves, 8);
        for (i, leaf) in state.leaves.iter().enumerate() {
            if i == 4 {
                assert_eq!(leaf.num_occurrences(), 1);
            } else {
                assert_eq!(leaf.num_occurrences(), 3);
            }
        }

        // Prune it from tree 0; it's now gone.
        state.prune_leaf(Leaf::new(4), 0);

        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_pruned.clone()));
        assert_eq!(state.num_leaves, 7);
        for (i, leaf) in state.leaves.iter().enumerate() {
            if i == 4 {
                assert_eq!(leaf.num_occurrences(), 0);
            } else {
                assert_eq!(leaf.num_occurrences(), 3);
            }
        }

        // Bring it back in tree 2.
        state.restore_leaf(Leaf::new(4), 2);

        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_restored.clone()));
        assert_eq!(state.num_leaves, 8);
        for (i, leaf) in state.leaves.iter().enumerate() {
            if i == 4 {
                assert_eq!(leaf.num_occurrences(), 1);
            } else {
                assert_eq!(leaf.num_occurrences(), 3);
            }
        }

        // Bring it back in tree 0.
        state.restore_leaf(Leaf::new(4), 0);

        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_restored.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_restored.clone()));
        assert_eq!(state.num_leaves, 8);
        for (i, leaf) in state.leaves.iter().enumerate() {
            if i == 4 {
                assert_eq!(leaf.num_occurrences(), 2);
            } else {
                assert_eq!(leaf.num_occurrences(), 3);
            }
        }

        // Bring it back in tree 1.
        state.restore_leaf(Leaf::new(4), 1);

        assert_eq!(state.num_trees(), 3);
        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_restored.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick_restored.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_restored.clone()));
        assert_eq!(state.num_leaves, 8);
        for leaf in &state.leaves {
            assert_eq!(leaf.num_occurrences(), 3);
        }
    }

    /// Check that suppress_node and restore_node behave correctly
    #[test]
    fn suppress_restore_node() {

        let (trees, newicks) = build_forest();
        let mut state = State::new(trees);

        // The Newick strings expected after pruning the leaves and not suppressing nodes
        let tree1_newick_pruned = String::from("(((a,c),d),((b),((g,e),h)));");
        let tree2_newick        = newicks[1].clone();
        let tree3_newick_pruned = String::from("((((h,(((g,e),c))),b),a),d);");

        // The Newick strings expected after suppressing nodes
        let tree1_newick_suppressed = String::from("(((a,c),d),(b,((g,e),h)));");
        let tree3_newick_suppressed = String::from("((((h,((g,e),c)),b),a),d);");

        let leaf    = Leaf::new(4);
        let parent0 = state.tree(0).parent(state.tree(0).leaf(leaf)).unwrap();
        let parent2 = state.tree(2).parent(state.tree(2).leaf(leaf)).unwrap();
        state.prune_leaf(leaf, 0);
        state.prune_leaf(leaf, 2);

        // Check that suppressing the parent of a leaf works correctly
        state.suppress_node(parent0, 0);

        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_suppressed.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_pruned.clone()));
    
        // Check that suppressing the parent of an internal node works correctly
        state.suppress_node(parent2, 2);

        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_suppressed.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_suppressed.clone()));

        // Restore them both
        state.restore_node(parent0, 0);
        state.restore_node(parent2, 2);

        assert_eq!(newick::format_tree(&state.trees[0]), Some(tree1_newick_pruned.clone()));
        assert_eq!(newick::format_tree(&state.trees[1]), Some(tree2_newick.clone()));
        assert_eq!(newick::format_tree(&state.trees[2]), Some(tree3_newick_pruned.clone()));
    }

    /// Test the correct behaviour of push/pop operations to manipulate the tree-child sequence.
    #[test]
    fn push_pop_tree_child_pair() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        assert_eq!(state.tc_seq.len(), 0);

        state.push_trivial_tree_child_pair(Leaf::new(3), Leaf::new(4));

        assert_eq!(state.tc_seq, vec![Pair::Trivial(Leaf::new(3), Leaf::new(4))]);

        state.push_non_trivial_tree_child_pair(Leaf::new(3), Leaf::new(5));

        assert_eq!(state.tc_seq, vec![
                   Pair::Trivial(Leaf::new(3), Leaf::new(4)),
                   Pair::NonTrivial(Leaf::new(3), Leaf::new(5))]);

        state.pop_tree_child_pair();

        assert_eq!(state.tc_seq, vec![Pair::Trivial(Leaf::new(3), Leaf::new(4))]);

        state.push_trivial_tree_child_pair(Leaf::new(6), Leaf::new(5));
        state.push_non_trivial_tree_child_pair(Leaf::new(6), Leaf::new(7));
        state.push_final_tree_child_pair(Leaf::new(0));

        assert_eq!(state.tc_seq(), vec![
                   Pair::Trivial(String::from("b"), String::from("f")),
                   Pair::Trivial(String::from("e"), String::from("g")),
                   Pair::NonTrivial(String::from("e"), String::from("h")),
                   Pair::Final(String::from("a"))]);
    }

    /// Test that we report the final leaf correctly (None if there is more than one leaf,
    /// Some(leaf) if leaf is the final remaining leaf).
    #[test]
    fn final_leaf() {

        let (trees, _) = build_forest();
        let mut state = State::new(trees);

        // We have more than one leaf, so we should get None
        assert_eq!(state.final_leaf(), None);

        // Pretend we have exactly one leaf left
        state.num_leaves = 1;
        for leaf in state.leaves.iter_mut() {
            leaf.decrease_num_occurrences();
            leaf.decrease_num_occurrences();
            leaf.decrease_num_occurrences();
        }
        state.leaf_mut(Leaf::new(4)).increase_num_occurrences();

        // This leaf should now be reported
        assert_eq!(state.final_leaf(), Some(Leaf::new(4)));

        // ... even if it occurs more than once
        state.leaf_mut(Leaf::new(4)).increase_num_occurrences();

        assert_eq!(state.final_leaf(), Some(Leaf::new(4)));
    }

    /// Non-destructively access the constructed tree-child sequence
    pub fn tc_seq<T>(state: &State<T>) -> &TcSeq<Leaf> {
        &state.tc_seq
    }

    /// Get access to a tree in this state
    pub fn tree<T>(state: &State<T>, tree: usize) -> &Tree<T> {
        &state.trees[tree]
    }

    /// Get access to a leaf record in this state
    pub fn leaf<T>(state: &State<T>, leaf: usize) -> &leaf::Leaf {
        &state.leaves[leaf]
    }

    /// The number of trivial cherries
    pub fn num_trivial_cherries<T>(state: &State<T>) -> usize {
        state.trivial_cherries.len()
    }

    /// Get access to a trivial cherry
    pub fn trivial_cherry<T>(state: &State<T>, index: usize) -> &cherry::Cherry {
        &state.trivial_cherries[index]
    }

    /// Get access to a non-trivial cherry
    pub fn non_trivial_cherry<T>(state: &State<T>, index: usize) -> &cherry::Cherry {
        &state.non_trivial_cherries[index]
    }
}
