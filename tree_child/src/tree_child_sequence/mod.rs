//! This module implements the algorithm for constructing a tree-child sequence for a set of trees.
//! The function to construct a tree-child sequence is `tree_child_sequence()`.

use std::fmt;
use tree::Tree;

mod channel;
mod master;
mod worker;
mod search;

use self::master::Master;
use self::search::Search;

/// An entry in a tree-child sequence
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Pair<T> {

    /// A pair (x, y) that represents a trivial cherry
    Trivial(T, T),

    /// A pair (x, y) that eliminates a non-trivial cherry
    NonTrivial(T, T),

    /// The final leaf left in every tree at the end of the sequence
    Final(T),
}

/// A tree-child sequence is just a sequence of `Pair`s
pub type TcSeq<T> = Vec<Pair<T>>;

/// Compute a tree-child sequence for a given set of trees
pub fn tree_child_sequence<T: Clone + Send + 'static>(
    trees:                    Vec<Tree<T>>,
    num_threads:              usize,
    poll_delay:               Option<usize>,
    limit_fanout:             bool,
    use_redundant_branch_opt: bool) -> TcSeq<T> {

    // Build the search state and eliminate initial trivial cherries
    let mut search = Search::new(trees, limit_fanout, use_redundant_branch_opt);
    search.resolve_trivial_cherries();

    // Do not start a search if the input is trivial
    if search.success() {
        search.tc_seq().unwrap()
    } else {
        Master::run(search, num_threads, poll_delay)
    }
}

/// Let's make pairs printable
impl<T: fmt::Display> fmt::Display for Pair<T> {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Pair::Trivial(u, v)    => write!(f, "({}, {})", u, v),
            Pair::NonTrivial(u, v) => write!(f, "({}, {})", u, v),
            Pair::Final(u)         => write!(f, "({}, -)", u),
        }
    }
}

#[cfg(test)]
mod tests {

    use newick;
    use std::fmt::Write;
    use tree::TreeBuilder;

    /// Test tree_child_sequence
    #[test]
    fn tree_child_sequence() {

        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick =
                "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };

        let seq = super::tree_child_sequence(trees, 32, Some(1), true, true);

        assert_eq!(seq.len(), 7);

        let mut string = String::new();
        let mut first  = true;
        write!(&mut string, "<").unwrap();
        for pair in seq {
            if first {
                first = false;
            } else {
                write!(&mut string, ", ").unwrap();
            }
            write!(&mut string, "{}", pair).unwrap();
        }
        write!(&mut string, ">").unwrap();

        assert!(
            ["<(d, c), (d, e), (b, c), (b, a), (c, e), (a, e), (e, -)>",
             "<(d, e), (d, c), (b, c), (b, a), (c, e), (a, e), (e, -)>",
             "<(b, a), (d, e), (d, c), (b, c), (c, e), (a, e), (e, -)>",
            ].contains(&&string[..]));
    }
}
