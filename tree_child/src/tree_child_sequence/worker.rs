//! This module implements the worker of the master-worker parallel implementation of the search.
//! A worker goes into idle state immediately after being spawned.  Before becoming idle, a worker
//! checks if it is the last thread to become idle and sends a `Result(None)` to the master to
//! indicate that a new search should be started.
//!
//! If a worker receives `None` from the master, it exits.  If it receives `Some` search, it starts
//! to execute this search.  Every `poll_delay` branches, it checks whether there are idle threads.
//! If so, it removes a branch from its topmost branch point and sends this work to the master to
//! be sent to a specific idle worker.  If the search ends unsuccessfully, the worker becomes idle
//! again, as before checking whether it is the last thread to become idle.  If the search
//! succeeds, the worker sends a `Result(Some(seq))` message to the master to trigger termination
//! of the search.

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

    /// The number of branches to explore before checking for idle threads
    poll_delay: Option<usize>,

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
    pub fn new(
        id:          usize,
        num_workers: usize,
        poll_delay:  Option<usize>,
        waiting:     Arc<RwLock<Vec<usize>>>,
        result:      Sender<FromWorker<T>>) -> Self {

        let (queue, work) = channel();
        let worker_state = WorkerState { id, num_workers, poll_delay, waiting, work, result };
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

                // Exit on receiving an empty message
                None => return,

                // Start a search we receive from the master
                Some(search) => {
                    let result = self.run_search(search);
                    self.send_result(result);
                }
            }
        }
    }

    /// Run a search and return the result
    fn run_search(&self, mut search: Search<T>) -> Option<TcSeq<T>> {

        // Terminate the search immediately if it has no chance of success (too many non-trivial
        // cherries)
        if search.can_succeed() {

            // Create a new branch point for the current state
            search.start_branch();

            if let Some(poll_delay) = self.poll_delay {
                // If we should poll for idle threads, do this.
                'l: loop {

                    // Run as many branching steps as indicated by poll_delay
                    for _ in 0..poll_delay {
                        if !search.branch() {
                            break 'l
                        }
                    }

                    // Now check whether there's an idle thread, first cheaply using a read lock.
                    if self.waiting.read().unwrap().len() > 0 {

                        // Try to pop a waiting thread of the waiting queue.  This may fail if some
                        // other thread grabbed it first
                        let recipient = self.waiting.write().unwrap().pop();

                        // If we did grab an idle thread, then ...
                        if let Some(recipient) = recipient {
                            if let Some(other_search) = search.split() {
                                // ... share some work with it if we have any.
                                self.share_work(recipient, other_search);
                            } else {
                                // ... push it back onto the idle queue if we don't have any work
                                // for it.
                                self.waiting.write().unwrap().push(recipient);
                            }
                        }
                    }
                }
            } else {
                // Otherwise, just run the search until done
                while search.branch() {}
            }

            // Return the tree-child sequence if we found one
            search.tc_seq()
        } else {
            None
        }
    }

    /// Send the result of the search back to the master
    fn send_result(&self, result: Option<TcSeq<T>>) {

        // We're done, go into idle state
        let mut waiting = self.waiting.write().unwrap();
        waiting.push(self.id);

        if result.is_some() {
            // If the search was successful, send the result to the master
            self.result.send(FromWorker::Result(result)).unwrap();
        } else if waiting.len() == self.num_workers {
            // Otherwise, send `None` back to the master to indicate a failed search only if this
            // is the last idle thread.
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
            |i| Worker::new(i, NUM_WORKERS, Some(1), waiting.clone(), sender.clone())).collect();
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
            |i| Worker::new(i, NUM_WORKERS, Some(1), waiting.clone(), sender.clone())).collect();
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
            |i| Worker::new(i, NUM_WORKERS, Some(1), waiting.clone(), sender.clone())).collect();
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
            let newick =
                "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
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
            |i| Worker::new(i, NUM_WORKERS, Some(1), waiting.clone(), sender.clone())).collect();
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
            let newick =
                "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
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
            |i| Worker::new(i, NUM_WORKERS, Some(1), waiting.clone(), sender.clone())).collect();
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
