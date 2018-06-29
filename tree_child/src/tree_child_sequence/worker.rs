use super::TcSeq;
use super::search::Search;

pub struct Worker<T> {

    /// The worker's search
    search: Search<T>,
}

impl<T: Clone> Worker<T> {

    /// Create a new worker
    pub fn new(search: Search<T>) -> Self {
        Worker { search }
    }

    //----------------------------------------------------------------------------------------------
    // Running the search
    //----------------------------------------------------------------------------------------------

    /// Recursively search for a tree-child sequence
    pub fn run(mut self) -> Option<TcSeq<T>> {
        if self.search.can_succeed() {
            self.search.start_branch();
            while self.search.branch() {}
            self.search.tc_seq()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {

    use newick;
    use std::fmt::Write;
    use super::*;
    use tree::TreeBuilder;

    /// Test successful search with parameter 0
    #[test]
    fn search_0_success() {
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "((a,g),(b,(c,e)));\n";
            let newick = String::from(newick) + newick + newick;
            newick::parse_forest(&mut builder, &newick).unwrap();
            builder.trees()
        };
        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();
        assert!(search.success());
        let seq = search.tc_seq().unwrap();
        assert_eq!(seq.len(), 5);
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
        assert_eq!(string, "<(c, e), (b, e), (a, g), (g, e), (e, -)>");
    }

    /// Test unsuccessful search with parameter 0
    #[test]
    fn search_0_fail() {
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "((a,b),c);\n(a,(b,c));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();
        assert!(!search.success());
        assert_eq!(Worker::new(search).run(), None);
    }

    /// Test successful search with parameter 1
    #[test]
    fn search_1_success() {
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "((a,b),c);\n(a,(b,c));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();
        assert!(!search.success());
        search.increase_max_weight();
        if let Some(seq) = Worker::new(search).run() {
            assert_eq!(seq.len(), 4);
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
            assert_eq!(string, "<(a, b), (b, c), (a, c), (c, -)>");
        } else {
            panic!("Search should have succeeded but failed");
        }
    }

    /// Test unsuccessful search with parameter 1
    #[test]
    fn search_1_fail() {
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();
        assert!(!search.success());
        search.increase_max_weight();
        assert_eq!(Worker::new(search).run(), None);
    }

    /// Test successful search with parameter 2
    #[test]
    fn search_2_success() {
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();
        assert!(!search.success());
        search.increase_max_weight();
        search.increase_max_weight();
        if let Some(seq) = Worker::new(search).run() {
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
        } else {
            panic!("Search should have succeeded but failed");
        }
    }
}
