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
pub fn tree_child_sequence<'a, Label, T>(trees: &'a [mut T]) -> TcSeq<Label>
where T: 'a + Tree<'a, Label> {
    let search = Search::new(trees);
    let mut k = 0;
    loop {
        if let Some(seq) = search.run(k) {
            return seq;
        }
        k += 1;
    }
}


/// The state of the search for a tree-child sequence
struct Search<'a, Label, T>
where T: 'a + Tree<'a, Label> {

    /// The trees for which to find a TC sequence
    trees: &'a[mut T],

    /// The information associated with the leaves during the search
    leaf_data: Vec<LeafData>,

    /// The list of trivial cherries
    trivial_cherries: Vec<(Leaf, Leaf)>,

    /// The list of non-trivial cherries
    non_trivial_cherries: Vec<(Leaf, Leaf, usize)>,
}


/// The data associated with a leaf
struct LeafData {

    /// The number of trees this leaf still occurs in
    num_occurrences: usize,

    /// The cherry this leaf is part of
    cherry: Option<CherryRef>,
}


/// Reference to a cherry.  Needs to distinguish between a trivial and a non-trivial cherry because
/// they are stored in different arrays
enum CherryRef {
    Trivial(usize),
    NonTrivial(usize),
}


impl<'a, Label, T> Search<'a, Label, T>
where T: 'a + Tree<'a, Label> {

    /// Create a new search state
    fn new(trees: &'a[mut T]) -> Self {
        let (trivial_cherries, non_trivial_cherries) = Self::find_cherries(trees);
        let leaf_data = Self::collect_leaf_data(trees, trivial_cherries, non_trivial_cherries);
        Search {
            trees,
            leaf_data,
            trivial_cherries,
            non_trivial_cherries,
        }
    }

    /// Find all cherries in a set of trees
    fn find_cherries(trees: &'a[T]) -> (Vec<(Leaf, Leaf)>, Vec<(Leaf, Leaf, usize)>) {

        let mut cherries = vec![];

        for tree in trees {
            for x in tree.leaves() {
                for y in tree.children(tree.parent(x)) {
                    if y.is_leaf() && x < y {
                        cherries.push((x, y));
                    }
                }
            }
        }
    }

    /// Construct the leaf data for all leaves in a set of trees
    fn collect_leaf_data(
        trees: &'a[T],
        trivial_cherries: Vec<(Leaf, Leaf)>,
        non_trivial_cherries: Vec<(Leaf, Leaf, usize)>) -> Vec<LeafData> {

        let mut leaf_data = vec![LeafData {
            num_occurrences: trees.len(),
            cherry:          None,
        }; trees[0].num_leaves()];

        for (i, (x, y)) in trivial_cherries.enumerate() {
            leaf_data[x.id()].cherry = CherryRef::Trivial(i);
            leaf_data[y.id()].cherry = CherryRef::Trivial(i);
        }

        for (i, (x, y, _)) in non_trivial_cherries.enumerate() {
            leaf_data[x.id()].cherry = CherryRef::NonTrivial(i);
            leaf_data[y.id()].cherry = CherryRef::NonTrivial(i);
        }

        leaf_data
    }
}
