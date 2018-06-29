use super::TcSeq;
use super::search::Search;
use super::worker::Worker;
use super::super::tree::Tree;

/// Implementation of the master thread
pub struct Master<T> {

    /// For now we have just one worker
    search: Search<T>,
}

impl<T: Clone> Master<T> {

    /// Create a new master
    pub fn new(trees: Vec<Tree<T>>, limit_fanout: bool, use_rendundant_branch_opt: bool) -> Self {
        let mut search = Search::new(trees, limit_fanout, use_rendundant_branch_opt);
        search.resolve_trivial_cherries();
        Master { search }
    }

    /// Run the master
    pub fn run(mut self) -> TcSeq<T> {
        if self.search.success() {
            // No need to spawn any workers; the input is trivial.
            return self.search.tc_seq().unwrap();
        } else {
            // We actually need to search for a solution
            loop {
                // Try to find a sequence for the next higher max_weight
                self.search.increase_max_weight();
                // If the worker succeeded, return its solution
                if let Some(seq) = Worker::new(self.search.clone()).run() {
                    return seq;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use newick;
    use std::fmt::Write;
    use tree::TreeBuilder;

    /// Test run
    #[test]
    fn run() {
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let master = Master::new(trees, true, true);
        let seq = master.run();
        assert_eq!(seq.len(), 7);
        let mut string = String::new();
        let mut first = true;
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
        assert_eq!(string, "<(d, c), (d, e), (b, c), (b, a), (c, e), (a, e), (e, -)>");
    }
}
