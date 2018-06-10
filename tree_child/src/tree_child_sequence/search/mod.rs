mod cherry;
mod leaf;
mod history;

use tree::{Tree, Leaf, Node};
use self::history::{History, Op};

/// The state of the search for a tree-child sequence
pub struct Search<T> {

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
    tc_seq: super::TcSeq,

    /// The history of operations performed on the current search path, so they can be undone
    history: History,
}

impl<T> Search<T> {

    //----------------------------------------------------------------------------------------------
    // Initialization code
    //----------------------------------------------------------------------------------------------

    /// Create a new search state
    pub fn new(trees: Vec<Tree<T>>) -> Self {

        let leaves = vec![leaf::Leaf::new(trees.len()); trees[0].leaf_count()];

        let mut search = Search {
            trees,
            leaves,
            trivial_cherries:     vec![],
            non_trivial_cherries: vec![],
            max_weight:           0,
            weight:               0,
            tc_seq:               vec![],
            history:              History::new(),
        };

        search.find_cherries();
        search
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
    // Running the search
    //----------------------------------------------------------------------------------------------


    /// Search for a tree-child sequence of weight k.
    pub fn run(mut self) -> super::TcSeq {
        self.resolve_trivial_cherries();
        loop {
            if self.recurse() {
                return self.tc_seq;
            }
            self.max_weight += 1;
        }
    }

    /// Recursively search for a tree-child sequence
    fn recurse(&mut self) -> bool {
        // TODO: Take care of the non-trivial cherries
        false
    }

    /// Eliminate all trivial cherries in the current search state.
    fn resolve_trivial_cherries(&mut self) {
        while let Some(cherry) = self.do_pop_trivial_cherry() {

            // Order the elements of the cherry so v is guaranteed to be in all
            // trees.  (This is true for at least one of u and v).
            let (u, v) = {
                let (u, v) = cherry.leaves();
                if self.leaf(v).num_occurrences() < self.num_trees() {
                    (v, u)
                } else {
                    (u, v)
                }
            };

            // Add (u, v) as a cherry to the cherry picking sequence
            self.do_record_tree_child_pair(u, v);

            // Prune u from every tree that has the cherry (u, v)
            for tree in cherry.trees() {
                self.do_prune_leaf(u, *tree);
            }
        }
    }

    //----------------------------------------------------------------------------------------------
    // Search operations
    //----------------------------------------------------------------------------------------------

    /// Add a trivial cherry
    fn do_add_trivial_cherry(&mut self, cherry: cherry::Cherry) {
        self.history.record_op(Op::AddTrivialCherry);
        self.add_trivial_cherry(cherry);
    }

    /// Undo the addition of a trivial cherry
    fn undo_add_trivial_cherry(&mut self) {
        self.pop_trivial_cherry();
    }

    /// Add a non-trivial cherry
    fn do_add_non_trivial_cherry(&mut self, cherry: cherry::Cherry) {
        self.history.record_op(Op::AddNonTrivialCherry);
        self.add_non_trivial_cherry(cherry);
    }

    /// Undo the addition of a non-trivial cherry
    fn undo_add_non_trivial_cherry(&mut self) {
        self.pop_non_trivial_cherry();
    }

    /// Remove the next trivial cherry and return it
    fn do_pop_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.pop_trivial_cherry().map(|cherry| {
            self.history.record_op(Op::PopTrivialCherry(cherry.clone()));
            cherry
        })
    }

    /// Undo popping a trivial cherry
    fn undo_pop_trivial_cherry(&mut self, cherry: cherry::Cherry) {
        self.add_trivial_cherry(cherry);
    }

    /// Remove the next non-trivial cherry and return it
    fn do_pop_non_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.pop_non_trivial_cherry().map(|cherry| {
            self.history.record_op(Op::PopNonTrivialCherry(cherry.clone()));
            cherry
        })
    }

    /// Undo popping a non-trivial cherry
    fn undo_pop_non_trivial_cherry(&mut self, cherry: cherry::Cherry) {
        self.add_non_trivial_cherry(cherry);
    }

    /// Remove a cherry indexed by the given cherry reference
    fn do_remove_cherry(&mut self, cherry_ref: cherry::Ref) -> cherry::Cherry {
        let cherry = self.remove_cherry(cherry_ref);

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
        self.restore_trivial_cherry(ix, cherry);
    }

    /// Undo the removal of a non-trivial cherry
    fn undo_remove_non_trivial_cherry(&mut self, ix: usize, cherry: cherry::Cherry) {
        self.restore_non_trivial_cherry(ix, cherry);
    }

    /// Record a newly detected cherry
    fn do_record_cherry(&mut self, u: Leaf, v: Leaf, tree: usize) {
        let cherry_ref = self.record_cherry(u, v, tree);
        self.history.record_op(Op::RecordCherry(cherry_ref));
    }

    /// Undo recording a cherry
    fn undo_record_cherry(&mut self, cherry_ref: cherry::Ref) {
        self.forget_cherry(cherry_ref);
    }

    /// Prune a leaf from a given tree
    fn do_prune_leaf(&mut self, leaf: Leaf, tree: usize) {

        // Prune the leaf and suppress the parent if it exists
        self.history.record_op(Op::PruneLeaf(leaf, tree));
        if let Some(parent) = self.prune_leaf(leaf, tree) {
            self.do_suppress_node(parent, tree);
        }

        // Check whether this has created a new trivial cherry
        if let Some(cherry_ref) = self.check_for_trivial_cherry(leaf) {
            let cherry = self.do_remove_cherry(cherry_ref);
            self.do_add_trivial_cherry(cherry);
        }
    }

    /// Undo the pruning of a leaf
    fn undo_prune_leaf(&mut self,leaf: Leaf, tree: usize) {
        self.restore_leaf(leaf, tree);
    }

    /// Suppress a node
    fn do_suppress_node(&mut self, node: Node, tree: usize) {

        // Suppress the node
        self.history.record_op(Op::SuppressNode(node, tree));
        let child = self.suppress_node(node, tree);

        // Check whether this has created a new cherry
        if let Some((u, v)) = self.check_for_cherry(child, tree) {
            self.do_record_cherry(u, v, tree);
        }
    }

    /// Undo the suppression of a node
    fn undo_suppress_node(&mut self, node: Node, tree: usize) {
        self.restore_node(node, tree);
    }

    /// Add a cherry to the cherry picking sequence
    fn do_record_tree_child_pair(&mut self, u: Leaf, v: Leaf) {
        self.history.record_op(Op::RecordTreeChildPair);
        self.tc_seq.push(super::Pair::Reduce(u, v));
    }

    /// Undo the recording of a cherry
    fn undo_record_tree_child_pair(&mut self) {
        self.tc_seq.pop();
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the lists of cherries
    //----------------------------------------------------------------------------------------------

    /// Record information about the given cherry (u, v) occurring in trees.
    fn record_cherry(&mut self, u: Leaf, v: Leaf, tree: usize) -> cherry::Ref {
//
//        // See whether we already have a cherry (u, v) on record
//        let u_cherries = &self.leaf_data[u.id()].cherries;
//        let cherry_ref = u_cherries.iter().find(|cherry_ref| {
//            let cherry = self.cherry(**cherry_ref);
//            (cherry.leaves.0).0 == v || (cherry.leaves.1).0 == v
//        }).map(|cherry_ref| *cherry_ref);
//
//        // Add the current tree to the list of trees for this cherry or create a new cherry
//        let cherry_ref = if let Some(cherry_ref) = cherry_ref {
//            self.cherry_mut(cherry_ref).trees.push(tree);
//            cherry_ref
//        } else {
//            let cherry_data = cherry::Cherry {
//                u, v,
//                uix: Default::default(),
//                vix: Default::default(),
//                trees:  vec![tree],
//            };
//            self.add_non_trivial_cherry(cherry_data);
//    };
//
//        // Mark the cherry as trivial if adding the new occurrence made it trivial
//        let cherry_occurrences = self.cherry(cherry_ref).trees.len();
//        let leaf_occurrences = min(
//            self.leaf_data[u.id()].num_occurrences,
//            self.leaf_data[v.id()].num_occurrences);
//
//        if leaf_occurrences == cherry_occurrences {
//            let cherry_data = self.remove_cherry(cherry_ref);
//            self.add_trivial_cherry(cherry_data);
//        }

        // TODO: This is a dummy
        cherry::Ref::Trivial(0)
    }

    /// Forget a cherry that was previously recorded
    fn forget_cherry(&mut self, cherry_ref: cherry::Ref) {
        self.cherry_mut(cherry_ref).pop_tree();
    }

    /// Check whether the given leaf is part of a trivial cherry
    fn check_for_trivial_cherry(&mut self, leaf: Leaf) -> Option<cherry::Ref> {

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
    fn check_for_cherry(&mut self, node: Node, tree: usize) -> Option<(Leaf, Leaf)> {
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

    /// Add a trivial cherry
    fn add_trivial_cherry(&mut self, mut cherry: cherry::Cherry) -> cherry::Ref {
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

    /// Add a non-trivial cherry
    fn add_non_trivial_cherry(&mut self, mut cherry: cherry::Cherry) -> cherry::Ref {
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
    fn pop_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.trivial_cherries.pop().map(|cherry| {
            let (u, v)     = cherry.leaves();
            let (uix, vix) = cherry.indices();
            self.remove_cherry_ref(u, uix);
            self.remove_cherry_ref(v, vix);
            cherry
        })
    }

    /// Pop a non-trivial cherry
    fn pop_non_trivial_cherry(&mut self) -> Option<cherry::Cherry> {
        self.non_trivial_cherries.pop().map(|cherry| {
            let (u, v)     = cherry.leaves();
            let (uix, vix) = cherry.indices();
            self.remove_cherry_ref(u, uix);
            self.remove_cherry_ref(v, vix);
            cherry
        })
    }

    /// Remove a cherry
    fn remove_cherry(&mut self, cherry_ref: cherry::Ref) -> cherry::Cherry {

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
            self.replace_cherry_ref(u, uix, cherry_ref);
            self.replace_cherry_ref(v, vix, cherry_ref);
        }

        // Now remove all references to the removed cherry
        let (u, v)     = cherry.leaves();
        let (uix, vix) = cherry.indices();
        self.remove_cherry_ref(u, uix);
        self.remove_cherry_ref(v, vix);

        cherry
    }

    /// Restore a trivial cherry
    fn restore_trivial_cherry(&mut self, index: usize, cherry: cherry::Cherry) {
        // TODO
    }

    /// Restore a non-trivial cherry
    fn restore_non_trivial_cherry(&mut self, index: usize, cherry: cherry::Cherry) {
        // TODO
    }

    /// Replace the cherry::Ref at the given position
    fn replace_cherry_ref(&mut self, leaf: Leaf, index: usize, cherry_ref: cherry::Ref) {
        self.leaf_mut(leaf).replace_cherry(index, cherry_ref);
    }

    /// Remove the given cherry ref
    fn remove_cherry_ref(&mut self, leaf: Leaf, index: usize) {
        self.leaf_mut(leaf).remove_cherry(index);
        if index < self.leaf(leaf).num_cherries() {
            let cherry_ref = self.leaf(leaf).cherry(index);
            self.replace_leaf_ref(leaf, index, cherry_ref);
        }
    }

    /// Restore a cherry ref
    fn restore_cherry_ref(&mut self, leaf: Leaf, index: usize, cherry_ref: cherry::Ref) {
        // TODO
    }

    /// Adjust a leaf reference stored in a given cherry
    fn replace_leaf_ref(&mut self, leaf: Leaf, index: usize, cherry_ref: cherry::Ref) {
        self.cherry_mut(cherry_ref).set_index(leaf, index);
    }

    //----------------------------------------------------------------------------------------------
    // Primitives to manipulate the trees
    //----------------------------------------------------------------------------------------------

    /// Prune a leaf from a tree
    fn prune_leaf(&mut self, leaf: Leaf, tree: usize) -> Option<Node> {
        self.tree_mut(tree).prune_leaf(leaf)
    }

    /// Restore a leaf that was previously pruned
    fn restore_leaf(&mut self, leaf: Leaf, tree: usize) {
        self.tree_mut(tree).restore_leaf(leaf)
    }

    /// Suppress an internal node
    fn suppress_node(&mut self, node: Node, tree: usize) -> Node {
        self.tree_mut(tree).suppress_node(node)
    }

    /// Restore an internal node
    fn restore_node(&mut self, node: Node, tree: usize) {
        self.tree_mut(tree).restore_node(node)
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
    fn leaf(&self, leaf: Leaf)-> &leaf::Leaf {
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
    fn num_trees(&self) -> usize {
        self.trees.len()
    }
}
