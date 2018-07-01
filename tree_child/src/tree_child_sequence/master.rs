use std::mem;
use std::sync::{Arc, RwLock};
use std::sync::mpsc::{Receiver, channel};
use super::TcSeq;
use super::search::Search;
use super::worker::Worker;
use super::super::tree::Tree;

/// The master thread
pub struct Master<T> {

    /// The problem instance to be solved
    search: Search<T>,

    /// The worker threads controlled by this master,
    workers: Vec<Worker<T>>,

    /// The idle queue
    waiting: Arc<RwLock<Vec<usize>>>,

    /// The queue used to receive messages from the workers
    queue: Receiver<Option<TcSeq<T>>>,
}

impl<T: Clone + Send + 'static> Master<T> {

    /// Initialize the master
    pub fn new(trees: Vec<Tree<T>>, num_workers: usize, limit_fanout: bool, use_rendundant_branch_opt: bool) -> Self {
        let search             = Search::new(trees, limit_fanout, use_rendundant_branch_opt);
        let (sender, receiver) = channel();
        let waiting            = Arc::new(RwLock::new(vec![]));
        let workers            = (0..num_workers).map(|i| Worker::new(i, num_workers, waiting.clone(), sender.clone())).collect();
        Master { search, workers, waiting, queue: receiver }
    }

    /// Run the master thread
    pub fn run(mut self) -> TcSeq<T> {
        self.search.resolve_trivial_cherries();
        loop {
            match self.queue.recv().unwrap() {
                Some(seq) => { self.stop_workers(); return seq; },
                None      => self.start_new_search(),
            }
        }
    }

    /// Start a new search
    fn start_new_search(&mut self) {
        self.search.increase_max_weight();
        let worker = self.waiting.write().unwrap().pop().unwrap();
        self.workers[worker].work_on(self.search.clone());
    }

    /// Stop all workers
    fn stop_workers(&mut self) {
        let workers = mem::replace(&mut self.workers, vec![]);
        for worker in workers {
            worker.quit();
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
        let master = Master::new(trees, 32, true, true);
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
