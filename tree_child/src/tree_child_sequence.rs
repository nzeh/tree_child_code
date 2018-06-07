use tree::traits::Id;
use tree::traits::Tree;

/// An entry in a tree-child sequence
pub enum Pair<T> {

    /// A pair (x, y) that eliminates x from every tree that has (x, y) as a cherry
    Reduce(T, T),

    /// The final leaf left in every tree at the end of the sequence
    Final(T),
}


/// A tree-child sequence is just a sequence of pairs
pub type TcSeq<T> = Vec<Pair<T>>;


/// Compute a tree-child sequence for a given set of trees
pub fn tree_child_sequence<'a, Label, T>(trees: &'a [T]) -> TcSeq<Label>
where T:     Tree<'a, Label> + Clone,
      Label: 'a {
    Search::new(trees).run()
}


/// The state of the search for a tree-child sequence
struct Search<'a, Label, T>
where T:     'a + Tree<'a, Label>,
      Label: 'a {

    /// The trees for which to find a TC sequence
    trees: Vec<T>,

    /// The information associated with the leaves during the search
    leaf_data: Vec<LeafData>,

    /// The list of trivial cherries.  For each cherry, we store references to the leaves, along
    /// with the entries in their cherry lists.
    trivial_cherries: Vec<CherryData<T::Leaf>>,

    /// The list of non-trivial cherries.  For each cherry, we store references to the leaves,
    /// along with the entries in their cherry lists.  We also store the number of trees that
    /// contain each cherry to be able to check quickly when a cherry becomes trivial.
    non_trivial_cherries: Vec<CherryData<T::Leaf>>,

    /// The maximum allowed weight of the constructed sequence
    max_weight: usize,

    /// The weight of the current tree-child sequence
    weight: usize,

    /// The currently constructed tree-child sequence
    tc_seq: TcSeq<Label>,

    /// The history of operations performed on the current search path, so they can be undone
    history: History<T::Leaf, T::Node>,
}


/// The data associated with a cherry
#[derive(Clone)]
struct CherryData<Leaf> {

    /// The two leaves this cherry is composed of, including references to the entries in their
    /// cherry lists
    leaves: (LeafRef<Leaf>, LeafRef<Leaf>),

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
struct LeafRef<Leaf>(Leaf, usize);


type History<Leaf, Node> = Vec<Operation<Leaf, Node>>;


/// The operations we perform
#[derive(Clone)]
enum Operation<Leaf, Node> {

    /// Remove a cherry from the list of non-trivial cherries
    RemoveTrivialCherry(CherryData<Leaf>),

    /// Prune a leaf from a tree
    PruneLeaf(usize, Leaf),

    /// Remove later
    Phantom(Node),
}


/// A snapshot of the current search state
struct Snapshot(usize);


impl<'a, Label, T> Search<'a, Label, T>
where T: Tree<'a, Label> + Clone {

    /// Create a new search state
    fn new(trees: &'a [T]) -> Self {

        let cherries = Self::find_cherries(trees);
        let (leaf_data, trivial_cherries, non_trivial_cherries) =
            Self::classify_cherries(trees.len(), trees[0].leaf_count(), cherries);

        Search {
            trees: Vec::from(trees),
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
    fn find_cherries(trees: &'a [T]) -> Vec<(T::Leaf, T::Leaf, usize)> {

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
        mut cherries: Vec<(T::Leaf, T::Leaf, usize)>) ->
        (Vec<LeafData>, Vec<CherryData<T::Leaf>>, Vec<CherryData<T::Leaf>>) {

        /// Record information about the given cherry (u, v) occurring in trees.
        fn record_cherry<Leaf: Copy + Id>(
            num_trees:               usize,
            leaf_data:               &mut Vec<LeafData>,
            trivial_cherries:        &mut Vec<CherryData<Leaf>>,
            non_trivial_cherries:    &mut Vec<CherryData<Leaf>>,
            u: Leaf, v: Leaf, trees: Vec<usize>) {

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

        // Initially, every leaf occurs in all trees and participates in no cherries
        let mut leaf_data = vec![LeafData {
            num_occurrences: num_trees,
            cherries:        vec![],
        }; num_leaves];

        // We haven't discovered any trivial or non-trivial cherries yet.
        let mut trivial_cherries     = vec![];
        let mut non_trivial_cherries = vec![];

        // The members of the current cherry and the trees that have this cherry
        let mut u     = None;
        let mut v     = None;
        let mut trees = vec![];

        cherries.sort_unstable();
        for (x, y, t) in cherries {

            // If the previous cherry did not involve x and y, then record information about the
            // previous cherry and initialize (u, v) to be the next cherry.
            if u != Some(x) || v != Some(y) {
                // Record the previous cherry only if it wasn't None.
                if let (Some(u_), Some(v_)) = (u, v) {
                    record_cherry(num_trees,
                                  &mut leaf_data, &mut trivial_cherries, &mut non_trivial_cherries,
                                  u_, v_, trees);
                }
                u     = Some(x);
                v     = Some(y);
                trees = vec![];
            }

            // Add t to the list of trees containing the current cherry (u, v)
            trees.push(t);
        }

        // Record the final cherry.
        if let (Some(u_), Some(v_)) = (u, v) {
            record_cherry(num_trees,
                          &mut leaf_data, &mut trivial_cherries, &mut non_trivial_cherries,
                          u_, v_, trees);
        }

        (leaf_data, trivial_cherries, non_trivial_cherries)
    }

    /// Search for a tree-child sequence of weight k.
    fn run(mut self) -> TcSeq<Label> {
        loop {
            if self.recurse() {
                return self.tc_seq;
            }
            self.max_weight += 1;
        }
    }

    /// Recursively search for a tree-child sequence
    fn recurse(&mut self) -> bool {
        let snapshot = self.take_snapshot();
        self.resolve_trivial_cherries();
        if self.resolve_non_trivial_cherries() {
            return true
        }
        self.rewind_to_snapshot(snapshot);
        false
    }

    /// Eliminate all trivial cherries in the current search state.
    fn resolve_trivial_cherries(&mut self) {
        while let Some(cherry) = self.remove_trivial_cherry() {
            let (x, y) = {
                let (LeafRef(x, _), LeafRef(y, _)) = cherry.leaves;
                if self.leaf_data[y.id()].num_occurrences < self.trees.len() {
                    (y, x)
                } else {
                    (x, y)
                }
            };
            for tree in cherry.trees {
                self.prune_leaf(tree, x);
            }
        }
    }

    /// Eliminate all non-trivial cherries
    fn resolve_non_trivial_cherries(&mut self) -> bool {
        // TODO
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
                    Operation::Phantom(_) => {} // Remove later
                }
            }
        }
    }

    /// Remove the next trivial cherry and return it
    fn remove_trivial_cherry(&mut self) -> Option<CherryData<T::Leaf>> {
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
    fn undo_remove_trivial_cherry(&mut self, mut cherry: CherryData<T::Leaf>) {
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
    fn adjust_last_cherry(&mut self, leaf_ref: LeafRef<T::Leaf>) {
        // TODO
    }

    /// Prune a leaf from a given tree
    fn prune_leaf(&mut self, tree: usize, leaf: T::Leaf) {
        // TODO: self.trees[tree].prune_leaf(leaf);
        self.history.push(Operation::PruneLeaf(tree, leaf));
    }

    /// Undo the pruning of a leaf
    fn undo_prune_leaf(&mut self, tree: usize, leaf: T::Leaf) {
        // TODO
    }
}
