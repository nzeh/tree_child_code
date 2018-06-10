use std::cmp::min;
use std::mem;
use super::cherry;
use super::leaf;
use tree::{Tree, Leaf, Node};

/// The state of the search for a tree-child sequence
pub struct State<T> {

    /// The trees for which to find a TC sequence
    trees: Vec<Tree<T>>,

    /// The information associated with the leaves during the search
    leaves: Vec<leaf::Leaf>,

    /// The list of trivial cherries.  For each cherry, we store references to the leaves, along
    /// with the entries in their cherry lists.
    trivial_cherries: Vec<cherry::Cherry>,

    /// The list of non-trivial cherries.  For each cherry, we store references to the leaves,
    /// along with the entries in their cherry lists.  We also store the number of trees that
    /// contain each cherry to be able to check quickly when a cherry becomes trivial.
    non_trivial_cherries: Vec<cherry::Cherry>,

    /// The maximum allowed weight of the constructed sequence
    max_weight: usize,

    /// The weight of the current tree-child sequence
    weight: usize,

    /// The currently constructed tree-child sequence
    tc_seq: super::super::TcSeq,
}

impl<T> State<T> {

    //----------------------------------------------------------------------------------------------
    // Initialization code
    //----------------------------------------------------------------------------------------------

    /// Create a new search state
    pub fn new(trees: Vec<Tree<T>>) -> Self {

        let leaves = vec![leaf::Leaf::new(trees.len()); trees[0].leaf_count()];

        let mut state = State {
            trees,
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
                if let Some(p) = tree.parent(u) {
                    for v in tree.children(p) {
                        if let (Some(u_), Some(v_)) = (tree.leaf_id(u), tree.leaf_id(v)) {
                            if u_ < v_ {
                                cherries.push((u_, v_, i));
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

    pub fn increase_max_weight(&mut self) {
        self.max_weight += 1;
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the lists of cherries
    //----------------------------------------------------------------------------------------------

    /// Record information about the given cherry (u, v) occurring in trees.
    pub fn record_cherry(&mut self, u: Leaf, v: Leaf, tree: usize) -> cherry::Ref {

        // See whether we already have a cherry (u, v) on record
        let cherry_ref = self.leaf(u).cherries().find(|cherry_ref| {
            let (x, y) = self.cherry(**cherry_ref).leaves();
            x == v || y == v
        }).map(|cherry_ref| *cherry_ref);

        // Add the current tree to the list of trees for this cherry or create a new cherry
        let cherry_ref = if let Some(cherry_ref) = cherry_ref {
            self.cherry_mut(cherry_ref).push_tree(tree);
            cherry_ref
        } else {
            self.push_non_trivial_cherry(cherry::Cherry::new(u, v, tree))
        };

        // Mark the cherry as trivial if adding the new occurrence made it trivial
        let cherry_occurrences = self.cherry(cherry_ref).num_occurrences();
        let leaf_occurrences = min(
            self.leaf(u).num_occurrences(),
            self.leaf(v).num_occurrences());

        if leaf_occurrences == cherry_occurrences {
            let cherry = self.remove_cherry(cherry_ref);
            self.push_trivial_cherry(cherry)
        } else {
            cherry_ref
        }
    }

    /// Forget a cherry that was previously recorded
    pub fn forget_cherry(&mut self, cherry_ref: cherry::Ref) {
        self.cherry_mut(cherry_ref).pop_tree();
        if self.cherry(cherry_ref).num_occurrences() == 0 {
            self.remove_cherry(cherry_ref);
        } else {
            if let cherry::Ref::Trivial(_) = cherry_ref {
                let cherry = self.remove_cherry(cherry_ref);
                self.push_non_trivial_cherry(cherry);
            }
        }
    }

    /// Check whether the given leaf is part of a trivial cherry
    pub fn check_for_trivial_cherry(&mut self, leaf: Leaf) -> Option<cherry::Ref> {

        // The leaf can be part of a trivial cherry only if there is exactly one cherry involving
        // this leaf.
        let leaf = self.leaf(leaf);
        if leaf.num_cherries() == 1 {
            let cherry_ref = leaf.cherry(0);
            if leaf.num_occurrences() == self.cherry(cherry_ref).num_occurrences() {
                Some(cherry_ref)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Check whether the given node forms a cherry in the given tree
    pub fn check_for_cherry(&mut self, node: Node, tree: usize) -> Option<(Leaf, Leaf)> {
        let tree = self.tree(tree);
        if let Some(leaf) = tree.leaf_id(node) {
            if let Some(parent) = tree.parent(node) {
                for sib in tree.children(parent) {
                    if sib != node {
                        if let Some(sib) = tree.leaf_id(sib) {
                            return Some((leaf, sib));
                        }
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

    /// Push a cherry to then end of the list of non-trivial cherries
    pub fn push_non_trivial_cherry(&mut self, mut cherry: cherry::Cherry) -> cherry::Ref {
        let cherry_ref = cherry::Ref::Trivial(self.non_trivial_cherries.len());
        let (u, v)     = cherry.leaves();
        let uix        = self.leaf(u).num_cherries();
        let vix        = self.leaf(v).num_cherries();
        cherry.set_indices(uix, vix);
        self.leaf_mut(u).add_cherry(cherry_ref);
        self.leaf_mut(v).add_cherry(cherry_ref);
        self.non_trivial_cherries.push(cherry);
        cherry_ref
    }

    /// Pop a trivial cherry
    pub fn pop_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.trivial_cherries.pop().map(|cherry| {
            let (u, v)     = cherry.leaves();
            let (uix, vix) = cherry.indices();
            self.remove_cherry_ref(u, uix);
            self.remove_cherry_ref(v, vix);
            cherry
        })
    }

    /// Pop a non-trivial cherry
    pub fn pop_non_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.non_trivial_cherries.pop().map(|cherry| {
            let (u, v)     = cherry.leaves();
            let (uix, vix) = cherry.indices();
            self.remove_cherry_ref(u, uix);
            self.remove_cherry_ref(v, vix);
            cherry
        })
    }

    /// Remove a cherry
    pub fn remove_cherry(&mut self, cherry_ref: cherry::Ref) -> cherry::Cherry {

        // First remove the cherry from the list of cherries
        let (cherry, updates) = {

            let (cherry, replacement) = match cherry_ref {

                cherry::Ref::Trivial(ix) => {
                    let cherry = self.trivial_cherries.swap_remove(ix);
                    let replacement = if ix < self.trivial_cherries.len() {
                        Some(&self.trivial_cherries[ix])
                    } else {
                        None
                    };
                    (cherry, replacement)
                },

                cherry::Ref::NonTrivial(ix) => {
                    let cherry = self.non_trivial_cherries.swap_remove(ix);
                    let replacement = if ix < self.non_trivial_cherries.len() {
                        Some(&self.non_trivial_cherries[ix])
                    } else {
                        None
                    };
                    (cherry, replacement)
                },
            };

            (cherry, replacement.map(|rep| (rep.leaves(), rep.indices())))
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

    /// Restore a trivial cherry
    pub fn restore_trivial_cherry(&mut self, index: usize, mut cherry: cherry::Cherry) {

        // Restore references to the cherry to be restored
        let (u, v)     = cherry.leaves();
        let (uix, vix) = cherry.indices();
        self.restore_cherry_ref(u, uix, cherry::Ref::Trivial(index));
        self.restore_cherry_ref(v, vix, cherry::Ref::Trivial(index));

        // If the position is at the end of the list, then simply push the cherry; otherwise, do a
        // swap_remove in reverse.
        let num_cherries = self.trivial_cherries.len();
        if index < num_cherries {
            mem::swap(&mut cherry, &mut self.trivial_cherries[index]);
            let (x, y)     = cherry.leaves();
            let (xix, yix) = cherry.indices();
            self.leaf_mut(x).replace_cherry(xix, cherry::Ref::Trivial(num_cherries));
            self.leaf_mut(y).replace_cherry(yix, cherry::Ref::Trivial(num_cherries));
        }
        self.trivial_cherries.push(cherry);
    }

    /// Restore a non-trivial cherry
    pub fn restore_non_trivial_cherry(&mut self, index: usize, mut cherry: cherry::Cherry) {

        // Restore references to the cherry to be restored
        let (u, v)     = cherry.leaves();
        let (uix, vix) = cherry.indices();
        self.restore_cherry_ref(u, uix, cherry::Ref::NonTrivial(index));
        self.restore_cherry_ref(v, vix, cherry::Ref::NonTrivial(index));

        // If the position is at the end of the list, then simply push the cherry; otherwise, do a
        // swap_remove in reverse.
        let num_cherries = self.non_trivial_cherries.len();
        if index < num_cherries {
            mem::swap(&mut cherry, &mut self.non_trivial_cherries[index]);
            let (x, y)     = cherry.leaves();
            let (xix, yix) = cherry.indices();
            self.leaf_mut(x).replace_cherry(xix, cherry::Ref::Trivial(num_cherries));
            self.leaf_mut(y).replace_cherry(yix, cherry::Ref::Trivial(num_cherries));
        }
        self.non_trivial_cherries.push(cherry);
    }

    /// Remove the given cherry ref
    fn remove_cherry_ref(&mut self, leaf: Leaf, index: usize) {
        self.leaf_mut(leaf).remove_cherry(index);
        if index < self.leaf(leaf).num_cherries() {
            let cherry_ref = self.leaf(leaf).cherry(index);
            self.cherry_mut(cherry_ref).set_index(leaf, index);
        }
    }

    /// Restore a cherry ref
    fn restore_cherry_ref(&mut self, leaf: Leaf, index: usize, mut cherry_ref: cherry::Ref) {
        let num_cherries = self.leaf(leaf).num_cherries();
        if index < num_cherries {
            mem::swap(&mut cherry_ref, self.leaf_mut(leaf).cherry_mut(index));
            self.cherry_mut(cherry_ref).set_index(leaf, num_cherries);
        }
        self.leaf_mut(leaf).add_cherry(cherry_ref);
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the trees
    //----------------------------------------------------------------------------------------------

    /// Prune a leaf from a tree
    pub fn prune_leaf(&mut self, leaf: Leaf, tree: usize) -> Option<Node> {
        self.tree_mut(tree).prune_leaf(leaf)
    }

    /// Restore a leaf that was previously pruned
    pub fn restore_leaf(&mut self, leaf: Leaf, tree: usize) {
        self.tree_mut(tree).restore_leaf(leaf)
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

    /// Push a new pair to the end of the tree-child sequence
    pub fn push_tree_child_pair(&mut self, u: Leaf, v: Leaf) {
        self.tc_seq.push(super::super::Pair::Reduce(u, v));
    }

    /// Remove the last pair form the tree-child sequence
    pub fn pop_tree_child_pair(&mut self) {
        self.tc_seq.pop();
    }

    /// Retrieve the tree-child sequence
    pub fn tc_seq(self) -> super::super::TcSeq {
        self.tc_seq
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

    /// The number of trees
    pub fn num_trees(&self) -> usize {
        self.trees.len()
    }
}
