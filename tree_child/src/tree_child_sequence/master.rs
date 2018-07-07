//! This module implements the master thread that drives the search for a solution.  The master
//! thread is in charge of deepening the search until a tree-child sequence of the current weight
//! exists.  It assigns the whole search to one of the worker threads.  The worker threads check
//! whether other workers are idle.  If so, they split off part of their search space and send it
//! back to the master with a target thread to give this work to.  The master thread then sends
//! this work to the indicated worker thread.
//!
//! The current search iteration ends once master thread receives a Result message from a worker.
//! If this result message wraps `Some` tree-child sequence, the master instructs all workers to quit
//! and returns the returned tree-child sequence.  If it receives `None`, then the search was
//! unsuccessful and the master starts another iteration after increasing the target weight by one.

use std::mem;
use std::sync::{Arc, RwLock};
use std::sync::mpsc::{Receiver, channel};
use super::TcSeq;
use super::search::Search;
use super::worker::{Worker, FromWorker};
use super::super::tree::Tree;

/// The master thread
pub struct Master<T> {

    /// The problem instance to be solved
    search: Search<T>,

    /// The worker threads controlled by this master,
    workers: Vec<Worker<T>>,

    /// The idle queue, holds the IDs of all idle workers
    waiting: Arc<RwLock<Vec<usize>>>,

    /// The queue used to receive messages from the workers
    queue: Receiver<FromWorker<T>>,
}

impl<T: Clone + Send + 'static> Master<T> {

    /// Initialize the master
    ///
    /// - `trees` is the set of trees for which to construct a tree-child sequence
    /// - `num_workers` is the number of worker threads to be used for parallelizing the search
    /// - `poll_delay` is the number of branching steps a worker should complete before checking
    ///   for idle threads to share work with
    /// - `limit_fanout` controls whether a branch with too many non-trivial cherries should be
    ///   aborted.
    /// - `use_redundant_branch_opt` controls whether a branch should ignore non-trivial cherries
    ///   that were already resolved with the exact same set of trees in a previous branch.
    pub fn new(
        trees:                     Vec<Tree<T>>,
        num_workers:               usize,
        poll_delay:                Option<usize>,
        limit_fanout:              bool,
        use_rendundant_branch_opt: bool) -> Self {

        let search             = Search::new(trees, limit_fanout, use_rendundant_branch_opt);
        let (sender, receiver) = channel();
        let waiting            = Arc::new(RwLock::new(vec![]));
        let workers            = (0..num_workers)
            .map(|i| Worker::new(i, num_workers, poll_delay, waiting.clone(), sender.clone()))
            .collect();

        Master { search, workers, waiting, queue: receiver }
    }

    /// Run the master thread
    pub fn run(mut self) -> TcSeq<T> {

        // Resolve trivial cherries before starting the search
        self.search.resolve_trivial_cherries();

        // Do not start a search if the input is trivial
        if self.search.success() {
            self.stop_workers();
            return self.search.tc_seq().unwrap();
        }

        // Loop until we find a solution
        loop {
            match self.queue.recv().unwrap() {

                // Some worker reported success.  Stop the workers and return the result.
                FromWorker::Result(Some(seq)) => { self.stop_workers(); return seq; },

                // All workers failed, start a new search
                FromWorker::Result(None) => self.start_new_search(),

                // Some worker wants to share work with recipient.  Send it to recipient.
                FromWorker::WorkPackage(recipient, search) =>
                    self.workers[recipient].work_on(search),
            }
        }
    }

    /// Start a new search.
    fn start_new_search(&mut self) {
        self.search.increase_max_weight();
        let worker = self.waiting.write().unwrap().pop().unwrap();
        self.workers[worker].work_on(self.search.clone());
    }

    /// Stop all workers
    fn stop_workers(&mut self) {
        let workers = mem::replace(&mut self.workers, vec![]);
        for worker in workers { worker.quit(); }
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
            let newick =
                "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let master = Master::new(trees, 32, Some(1), true, true);
        let seq    = master.run();

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

        assert_eq!(string, "<(d, c), (d, e), (b, c), (b, a), (c, e), (a, e), (e, -)>");
    }
}
