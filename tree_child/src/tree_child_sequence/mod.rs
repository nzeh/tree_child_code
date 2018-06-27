use tree::{Tree, Leaf};

mod search;

/// An entry in a tree-child sequence
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
pub enum Pair<T> {

    /// A pair (x, y) that eliminates x from every tree that has (x, y) as a cherry
    Reduce(T, T),

    /// The final leaf left in every tree at the end of the sequence
    Final(T),
}


/// A tree-child sequence is just a sequence of pairs
pub type TcSeq<T> = Vec<Pair<T>>;


/// Compute a tree-child sequence for a given set of trees
pub fn tree_child_sequence<T: Clone>(trees: Vec<Tree<T>>) -> TcSeq<T> {
    search::Search::new(trees).run()
}

#[cfg(test)]
mod test_support {

    use std::fmt;
    use super::Pair;

    impl fmt::Display for Pair {

        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Pair::Reduce(u, v) => write!(f, "({}, {})", u.id(), v.id()),
                Pair::Final(u)     => write!(f, "({}, -)", u.id()),
            }
        }
    }
}
