use tree::{Leaf, Node, Tree};

/// An entry in a tree-child sequence
pub enum Pair {

    /// A pair (x, y) that eliminates x from every tree that has (x, y) as a cherry
    Reduce(Leaf, Leaf),

    /// The final leaf left in every tree at the end of the sequence
    Final(Leaf),
}


/// A tree-child sequence is just a sequence of pairs
pub type TcSeq = Vec<Pair>;


/// Compute a tree-child sequence for a given set of trees
pub fn tree_child_sequence<T>(trees: Vec<Tree<T>>) -> TcSeq {
    Search::new(trees).run()
}


/// The state of the search for a tree-child sequence
struct Search<T> {

    /// The trees for which to find a TC sequence
    trees: Vec<Tree<T>>,

    /// The information associated with the leaves during the search
    leaf_data: Vec<LeafData>,

    /// The list of trivial cherries.  For each cherry, we store references to the leaves, along
    /// with the entries in their cherry lists.
    trivial_cherries: Vec<CherryData>,

    /// The list of non-trivial cherries.  For each cherry, we store references to the leaves,
    /// along with the entries in their cherry lists.  We also store the number of trees that
    /// contain each cherry to be able to check quickly when a cherry becomes trivial.
    non_trivial_cherries: Vec<CherryData>,

    /// The maximum allowed weight of the constructed sequence
    max_weight: usize,

    /// The weight of the current tree-child sequence
    weight: usize,

    /// The currently constructed tree-child sequence
    tc_seq: TcSeq,

    /// The history of operations performed on the current search path, so they can be undone
    history: History,
}


/// The data associated with a cherry
#[derive(Clone)]
struct CherryData {

    /// The two leaves this cherry is composed of, including references to the entries in their
    /// cherry lists
    leaves: (LeafRef, LeafRef),

    /// The trees that have this cherry
    trees: Vec<usize>,
}


/// The data associated with a leaf
#[derive(Clone)]
struct LeafData {

    /// The number of trees this leaf still occurs in
    num_occurrences: usize,

    /// The cherry this leaf is part of
    cherries: Vec<CherryRef>,
}


/// Reference to a cherry.  Needs to distinguish between a trivial and a non-trivial cherry because
/// they are stored in different arrays
#[derive(Clone, Copy)]
enum CherryRef {
    Trivial(usize),
    NonTrivial(usize),
}


/// Reference to a leaf, including the corresponding entry in its cherry list
#[derive(Clone, Copy)]
struct LeafRef(Leaf, usize);


/// The history of operations applied to produce the current set of trees
type History = Vec<Operation>;


/// The operations we perform
#[derive(Clone)]
enum Operation {

    /// Remove a cherry from the list of non-trivial cherries
    RemoveTrivialCherry(CherryData),

    /// Prune a leaf from a tree
    PruneLeaf(usize, Leaf),

    /// Suppress a node from a tree
    SuppressNode(usize, Node),

    /// Add a cherry to the tree-child sequence
    RecordTreeChildPair,
}


/// A snapshot of the current search state
struct Snapshot(usize);


impl<T> Search<T> {

    /// Create a new search state
    fn new(trees: Vec<Tree<T>>) -> Self {

        let cherries = Self::find_cherries(&trees);
        let (leaf_data, trivial_cherries, non_trivial_cherries) =
            Self::classify_cherries(trees.len(), trees[0].leaf_count(), cherries);

        Search {
            trees,
            leaf_data,
            trivial_cherries,
            non_trivial_cherries,
            max_weight: 0,
            weight: 0,
            tc_seq: vec![],
            history: vec![],
        }
    }

    /// Find all cherries in a set of trees
    fn find_cherries(trees: &[Tree<T>]) -> Vec<(Leaf, Leaf, usize)> {

        let mut cherries = vec![];

        for (i, tree) in trees.iter().enumerate() {
            for x in tree.leaves() {
                if let Some(p) = tree.parent(x) {
                    for y in tree.children(p) {
                        if let (Some(x_), Some(y_)) = (tree.leaf_id(x), tree.leaf_id(y)) {
                            if x_ < y_ {
                                cherries.push((x_, y_, i));
                            }
                        }
                    }
                }
            }
        }

        cherries
    }

    /// Construct the leaf data for all leaves in a set of trees
    fn classify_cherries(
        num_trees:    usize,
        num_leaves:   usize,
        mut cherries: Vec<(Leaf, Leaf, usize)>) ->
        (Vec<LeafData>, Vec<CherryData>, Vec<CherryData>) {

        // Initially, every leaf occurs in all trees and participates in no cherries
        let mut leaf_data = vec![LeafData {
            num_occurrences: num_trees,
            cherries:        vec![],
        }; num_leaves];

        // We haven't discovered any trivial or non-trivial cherries yet.
        let mut trivial_cherries     = vec![];
        let mut non_trivial_cherries = vec![];

        // The members of the current cherry and the trees that have this cherry
        let mut cherry = None;
        let mut trees  = vec![];

        cherries.sort_unstable();
        for (x, y, t) in cherries {

            // If the previous cherry did not involve x and y, then record information about the
            // previous cherry and initialize (u, v) to be the next cherry.
            if cherry != Some((x, y)) {
                // Record the previous cherry only if it wasn't None.
                if let Some((u, v)) = cherry {
                    Self::record_cherry(num_trees,
                                        &mut leaf_data, &mut trivial_cherries, &mut non_trivial_cherries,
                                        u, v, trees);
                }
                cherry = Some((x, y));
                trees = vec![];
            }

            // Add t to the list of trees containing the current cherry (u, v)
            trees.push(t);
        }

        // Record the final cherry.
        if let Some((u, v)) = cherry {
            Self::record_cherry(num_trees,
                                &mut leaf_data, &mut trivial_cherries, &mut non_trivial_cherries,
                                u, v, trees);
        }

        (leaf_data, trivial_cherries, non_trivial_cherries)
    }

    /// Record information about the given cherry (u, v) occurring in trees.
    fn record_cherry(
        num_trees:            usize,
        leaf_data:            &mut Vec<LeafData>,
        trivial_cherries:     &mut Vec<CherryData>,
        non_trivial_cherries: &mut Vec<CherryData>,
        u:                    Leaf,
        v:                    Leaf,
        trees:                Vec<usize>) {

        // The number of trees containing this cherry
        let num_occurrences = trees.len();

        // Create the representation of this cherry
        let cherry_data = CherryData {
            leaves: (
                        LeafRef(u, leaf_data[u.id()].cherries.len()),
                        LeafRef(v, leaf_data[v.id()].cherries.len()),
                        ),
                        trees,
        };

        // Store this cherry in the list of trivial or non-trivial cherries and get a reference
        // to this entry in the cherry list
        let cherry_ref = if num_occurrences == num_trees {
            trivial_cherries.push(cherry_data);
            CherryRef::Trivial(trivial_cherries.len() - 1)
        } else {
            non_trivial_cherries.push(cherry_data);
            CherryRef::NonTrivial(non_trivial_cherries.len() - 1)
        };

        // Push a reference to the created cherry into the lists of cherries that u and v
        // participate in.
        leaf_data[u.id()].cherries.push(cherry_ref);
        leaf_data[v.id()].cherries.push(cherry_ref);
    }

    /// Search for a tree-child sequence of weight k.
    fn run(mut self) -> TcSeq {
        self.resolve_trivial_cherries();
        loop {
            if self.recurse() {
                return self.tc_seq;
            }
            self.max_weight += 1;
        }
    }

    /// Eliminate all trivial cherries in the current search state.
    fn resolve_trivial_cherries(&mut self) {
        while let Some(cherry) = self.remove_trivial_cherry() {

            // Order the elements of the cherry so y is guaranteed to be in all
            // trees.
            let (x, y) = {
                let (LeafRef(x, _), LeafRef(y, _)) = cherry.leaves;
                if self.leaf_data[y.id()].num_occurrences < self.trees.len() {
                    (y, x)
                } else {
                    (x, y)
                }
            };

            // Add (x, y) as a cherry to the cherry picking sequence
            self.record_tree_child_pair(x, y);

            // Prune x from every tree that has the cherry (x, y)
            for tree in cherry.trees {
                self.prune_leaf(tree, x);
            }
        }
    }

    /// Recursively search for a tree-child sequence
    fn recurse(&mut self) -> bool {
        // TODO: Take care of the non-trivial cherries
        false
    }

    /// Take a snapshot of the current search state
    fn take_snapshot(&mut self) -> Snapshot {
        Snapshot(self.history.len())
    }

    /// Rewind to the given snapshot
    fn rewind_to_snapshot(&mut self, snapshot: Snapshot) {
        let Snapshot(s) = snapshot;
        while self.history.len() > s {
            if let Some(op) = self.history.pop() {
                match op {
                    Operation::RemoveTrivialCherry(cherry) => self.undo_remove_trivial_cherry(cherry),
                    Operation::PruneLeaf(tree, leaf)       => self.undo_prune_leaf(tree, leaf),
                    Operation::SuppressNode(tree, node)    => self.undo_suppress_node(tree, node),
                    Operation::RecordTreeChildPair         => self.undo_record_tree_child_pair(),
                }
            }
        }
    }

    /// Add a new cherry to the list of current cherries
    fn add_cherry(&mut self, tree: usize, u: Leaf, v: Leaf) {

        let cherry_ref = if let Some(cherry_ref) = self.leaf_data[u.id()].cherries.iter().find(|cherry_ref| {
            let cherry = self.cherry(**cherry_ref);
            (cherry.leaves.0).0 == v || (cherry.leaves.1).0 == v
        }).map(|cherry_ref| *cherry_ref) {
            self.cherry_mut(cherry_ref).trees.push(tree);
            cherry_ref
        } else {
            let cherry_ref = CherryRef::NonTrivial(self.non_trivial_cherries.len());
            self.non_trivial_cherries.push(CherryData {
                leaves: (
                            LeafRef(u, self.leaf_data[u.id()].cherries.len()),
                            LeafRef(v, self.leaf_data[v.id()].cherries.len()),
                        ),
                trees: vec![tree],
            });
            self.leaf_data[u.id()].cherries.push(cherry_ref);
            self.leaf_data[v.id()].cherries.push(cherry_ref);
            cherry_ref
        };
    }

    /// Remove the next trivial cherry and return it
    fn remove_trivial_cherry(&mut self) -> Option<CherryData> {
        self.trivial_cherries.pop().map(|cherry| {
            let (x, y) = cherry.leaves;
            self.adjust_last_cherry(x);
            self.adjust_last_cherry(y);
            self.leaf_data[x.0.id()].cherries.swap_remove(x.1);
            self.leaf_data[y.0.id()].cherries.swap_remove(y.1);
            self.history.push(Operation::RemoveTrivialCherry(cherry.clone()));
            cherry
        })
    }

    /// Undo the removal of a trivial cherry
    fn undo_remove_trivial_cherry(&mut self, mut cherry: CherryData) {
        {
            let leaves = &mut cherry.leaves;
            let x      = &mut leaves.0;
            let y      = &mut leaves.1;
            x.1 = self.leaf_data[x.0.id()].cherries.len();
            y.1 = self.leaf_data[y.0.id()].cherries.len();
            self.leaf_data[x.0.id()].cherries.push(CherryRef::Trivial(self.trivial_cherries.len()));
            self.leaf_data[y.0.id()].cherries.push(CherryRef::Trivial(self.trivial_cherries.len()));
        }
        self.trivial_cherries.push(cherry);
    }

    /// Adjust the reference to the last cherry in a leaf's cherry list in preparation for moving
    /// it into the position indicated in the given LeafRef
    fn adjust_last_cherry(&mut self, leaf_ref: LeafRef) {
        let last_cherry_ref = *self.leaf_data[leaf_ref.0.id()].cherries.last().unwrap();
        let last_cherry     = self.cherry_mut(last_cherry_ref);
        if (last_cherry.leaves.0).0 == leaf_ref.0 {
            (last_cherry.leaves.0).1 = leaf_ref.1;
        } else {
            (last_cherry.leaves.1).1 = leaf_ref.1;
        }
    }

    /// Prune a leaf from a given tree
    fn prune_leaf(&mut self, tree: usize, leaf: Leaf) {
        let node   = self.trees[tree].leaf(leaf);
        let parent = self.trees[tree].parent(node);

        // Record that this leaf is now gone from one tree
        self.leaf_data[leaf.id()].num_occurrences -= 1;

        // Cut off the leaf
        self.trees[tree].prune_leaf(leaf);
        self.history.push(Operation::PruneLeaf(tree, leaf));

        // If this node has a parent, the parent needs to be suppressed
        if let Some(parent) = parent {
            self.suppress_node(tree, parent);
        }
    }

    /// Undo the pruning of a leaf
    fn undo_prune_leaf(&mut self, tree: usize, leaf: Leaf) {
        self.trees[tree].restore_leaf(leaf);
        self.leaf_data[leaf.id()].num_occurrences += 1;
    }

    /// Suppress a node
    fn suppress_node(&mut self, tree: usize, node: Node) {
        let child = self.trees[tree].suppress_node(node);
        self.history.push(Operation::SuppressNode(tree, node));

        // Check whether this has created new cherries
        self.detect_cherries(tree, child);
    }

    /// Undo the suppression of a node
    fn undo_suppress_node(&mut self, tree: usize, node: Node) {
        self.trees[tree].restore_node(node);
    }

    /// Check for cherries that have the given leaf as a member
    fn detect_cherries(&mut self, tree: usize, node: Node) {
        if let Some(parent) = self.trees[tree].parent(node) {
            let mut leaf_siblings = vec![];
            for child in self.trees[tree].children(parent) {
                if self.trees[tree].is_leaf(child) && child != node {
                    leaf_siblings.push(child);
                }
            }
            for sib in leaf_siblings {
                let sib  = self.trees[tree].leaf_id(sib).unwrap();
                let node = self.trees[tree].leaf_id(node).unwrap();
                self.add_cherry(tree, node, sib);
            }
        }
    }

    /// Add a cherry to the cherry picking sequence
    fn record_tree_child_pair(&mut self, u: Leaf, v: Leaf) {
        self.tc_seq.push(Pair::Reduce(u, v));
        self.history.push(Operation::RecordTreeChildPair);
    }

    /// Undo the recording of a cherry
    fn undo_record_tree_child_pair(&mut self) {
        self.tc_seq.pop();
    }

    /// Get a reference to a cherry
    fn cherry(&self, cherry_ref: CherryRef) -> &CherryData {
        match cherry_ref {
            CherryRef::Trivial(index)    => &self.trivial_cherries[index],
            CherryRef::NonTrivial(index) => &self.non_trivial_cherries[index],
        }
    }

    /// Get a mutable reference to a cherry
    fn cherry_mut(&mut self, cherry_ref: CherryRef) -> &mut CherryData {
        match cherry_ref {
            CherryRef::Trivial(index)    => &mut self.trivial_cherries[index],
            CherryRef::NonTrivial(index) => &mut self.non_trivial_cherries[index],
        }
    }
}
