use std::sync::{Arc, RwLock};
use std::sync::mpsc::{Sender, Receiver, channel};
use std::thread;
use super::TcSeq;
use super::search::Search;

/// The external interface of a worker used by the master
pub struct Worker<T> {

    /// The worker's thread
    thread: thread::JoinHandle<()>,

    /// The worker's sending end of the message queue
    queue: Sender<Option<Search<T>>>,
}

/// The internal state of a worker
struct WorkerState<T> {

    /// The ID of this worker
    id: usize,

    /// The total number of workers
    num_workers: usize,

    /// The idle queue
    waiting: Arc<RwLock<Vec<usize>>>,

    /// The queue used to receive work from the master
    work: Receiver<Option<Search<T>>>,

    /// The queue used to send results back to the master
    result: Sender<FromWorker<T>>,
}

/// The type of message a worker sends to the master
pub enum FromWorker<T> {

    /// The result of a computation
    Result(Option<TcSeq<T>>),

    /// Part of the work this worker is ready to share with another worker
    WorkPackage(usize, Search<T>),
}

impl<T: Clone + Send + 'static> Worker<T> {

    /// Create a new worker
    pub fn new(id: usize, num_workers: usize, waiting: Arc<RwLock<Vec<usize>>>, result: Sender<FromWorker<T>>) -> Self {
        let (queue, work) = channel();
        let worker_state = WorkerState { id, num_workers, waiting, work, result };
        let thread = thread::spawn(move || worker_state.run());
        Worker { thread, queue }
    }

    /// Send work to this thread
    pub fn work_on(&self, search: Search<T>) {
        self.queue.send(Some(search)).unwrap();
    }

    /// Quit the thread
    pub fn quit(self) {
        self.queue.send(None).unwrap();
        self.thread.join().unwrap();
    }
}

impl<T: Clone> WorkerState<T> {

    /// Recursively search for a tree-child sequence
    fn run(self) {
        self.send_result(None);
        loop {
            match self.work.recv().unwrap() {
                None         => return,
                Some(search) => {
                    let result = self.run_search(search);
                    self.send_result(result);
                }
            }
        }
    }

    /// Run a search and return the result
    fn run_search(&self, mut search: Search<T>) -> Option<TcSeq<T>> {
        if search.success() {
            return search.tc_seq();
        }
        if search.can_succeed() {
            search.start_branch();
            while search.branch() {
                if self.waiting.read().unwrap().len() > 0 {
                    let recipient = self.waiting.write().unwrap().pop();
                    if let Some(recipient) = recipient {
                        if let Some(other_search) = search.split() {
                            self.share_work(recipient, other_search);
                        } else {
                            self.waiting.write().unwrap().push(recipient);
                        }
                    }
                }
            }
            if let Some(seq) = search.tc_seq() {
                return Some(seq);
            }
        }
        None
    }

    /// Send the result of the search back to the master
    fn send_result(&self, result: Option<TcSeq<T>>) {
        let mut waiting = self.waiting.write().unwrap();
        waiting.push(self.id);
        if result.is_some() {
            self.result.send(FromWorker::Result(result)).unwrap();
        } if waiting.len() == self.num_workers {
            self.result.send(FromWorker::Result(None)).unwrap();
        }
    }

    /// Send part of my workload to another worker
    fn share_work(&self, recipient: usize, search: Search<T>) {
        self.result.send(FromWorker::WorkPackage(recipient, search)).unwrap();
    }
}

#[cfg(test)]
mod tests {

    use newick;
    use std::fmt::Write;
    use super::*;
    use tree::TreeBuilder;

    /// Test starting and stopping threads
    #[test]
    fn start_stop_workers() {
        const NUM_WORKERS: usize        = 32;
        let (sender, receiver)          = channel();
        let waiting                     = Arc::new(RwLock::new(vec![]));
        let workers: Vec<Worker<usize>> = (0..NUM_WORKERS).map(
            |i| Worker::new(i, NUM_WORKERS, waiting.clone(), sender.clone())).collect();
        match receiver.recv().unwrap() {
            FromWorker::Result(res) => assert!(res.is_none()),
            _                       => panic!("Expected a result, not a workload"),
        }
        for worker in workers {
            worker.quit();
        }
    }

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
        // Create search state and check that it's non-trivial
        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "((a,b),c);\n(a,(b,c));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };
        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();
        assert!(!search.success());

        const NUM_WORKERS: usize         = 32;
        let (sender, receiver)           = channel();
        let waiting                      = Arc::new(RwLock::new(vec![]));
        let workers: Vec<Worker<String>> = (0..NUM_WORKERS).map(
            |i| Worker::new(i, NUM_WORKERS, waiting.clone(), sender.clone())).collect();
        match receiver.recv().unwrap() {
            FromWorker::Result(res) => assert!(res.is_none()),
            _                       => panic!("Expected a result, not a workload"),
        }
        let i = waiting.write().unwrap().pop().unwrap();
        workers[i].work_on(search);
        loop {
            match receiver.recv().unwrap() {
                FromWorker::Result(None) => {
                    for worker in workers {
                        worker.quit();
                    }
                    return;
                },
                FromWorker::Result(Some(_)) => {
                    panic!("search_0_fail should have failed");
                },
                FromWorker::WorkPackage(recipient, search) => workers[recipient].work_on(search),
            }
        }
    }

    /// Test successful search with parameter 1
    #[test]
    fn search_1_success() {
        // Create a search state and check that it's non-trivial
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
        const NUM_WORKERS: usize         = 32;
        let (sender, receiver)           = channel();
        let waiting                      = Arc::new(RwLock::new(vec![]));
        let workers: Vec<Worker<String>> = (0..NUM_WORKERS).map(
            |i| Worker::new(i, NUM_WORKERS, waiting.clone(), sender.clone())).collect();
        match receiver.recv().unwrap() {
            FromWorker::Result(res) => assert!(res.is_none()),
            _                       => panic!("Expected a result, not a workload"),
        }
        let i = waiting.write().unwrap().pop().unwrap();
        workers[i].work_on(search);
        loop {
            match receiver.recv().unwrap() {
                FromWorker::Result(Some(seq)) => {
                    for worker in workers {
                        worker.quit();
                    }
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
                    return;
                },
                FromWorker::Result(None) => {
                    panic!("search_1_success should have succeeded");
                },
                FromWorker::WorkPackage(recipient, search) => workers[recipient].work_on(search),
            }
        }
    }

    /// Test unsuccessful search with parameter 1
    #[test]
    fn search_1_fail() {
        // Create a search state and check that it's non-trivial
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
        const NUM_WORKERS: usize         = 32;
        let (sender, receiver)           = channel();
        let waiting                      = Arc::new(RwLock::new(vec![]));
        let workers: Vec<Worker<String>> = (0..NUM_WORKERS).map(
            |i| Worker::new(i, NUM_WORKERS, waiting.clone(), sender.clone())).collect();
        match receiver.recv().unwrap() {
            FromWorker::Result(res) => assert!(res.is_none()),
            _                       => panic!("Expected a result, not a workload"),
        }
        let i = waiting.write().unwrap().pop().unwrap();
        workers[i].work_on(search);
        loop {
            match receiver.recv().unwrap() {
                FromWorker::Result(None) => {
                    for worker in workers {
                        worker.quit();
                    }
                    return;
                },
                FromWorker::Result(Some(_)) => {
                    panic!("search_1_fail should have failed");
                },
                FromWorker::WorkPackage(recipient, search) => workers[recipient].work_on(search),
            }
        }
    }

    /// Test successful search with parameter 2
    #[test]
    fn search_2_success() {
        // Create a search state and check that it's non-trivial
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
        const NUM_WORKERS: usize         = 32;
        let (sender, receiver)           = channel();
        let waiting                      = Arc::new(RwLock::new(vec![]));
        let workers: Vec<Worker<String>> = (0..NUM_WORKERS).map(
            |i| Worker::new(i, NUM_WORKERS, waiting.clone(), sender.clone())).collect();
        match receiver.recv().unwrap() {
            FromWorker::Result(res) => assert!(res.is_none()),
            _                       => panic!("Expected a result, not a workload"),
        }
        let i = waiting.write().unwrap().pop().unwrap();
        workers[i].work_on(search);
        loop {
            match receiver.recv().unwrap() {
                FromWorker::Result(Some(seq)) => {
                    for worker in workers {
                        worker.quit();
                    }
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
                    return;
                },
                FromWorker::Result(None) => {
                    panic!("search_1_success should have succeeded");
                },
                FromWorker::WorkPackage(recipient, search) => workers[recipient].work_on(search),
            }
        }
    }
}
