use tree::{Tree, Leaf};

mod search;

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
    search::Search::new(trees).run()
}
