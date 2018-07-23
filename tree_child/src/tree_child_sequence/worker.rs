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

use std::clone::Clone;
use std::thread;
use std::thread::{JoinHandle, yield_now};
use super::TcSeq;
use super::channel::{Receiver, Sender, Status};
use super::search::Search;

/// The structure representing a worker
pub struct Worker<T> {

    /// The ID of this worker
    id: usize,

    /// The communication interface to the master
    master: Sender<Option<TcSeq<T>>>,

    /// The communication interfaces to other workers
    workers: Vec<Sender<Message<T>>>,
    
    /// The incoming message queue
    incoming: Receiver<Message<T>>,

    /// The number of branches to explore before checking for idle threads
    poll_delay: Option<usize>,
}

impl<T: Clone + Send + 'static> Worker<T> {

    /// Create a new worker
    pub fn spawn(
        id:         usize,
        master:     Sender<Option<TcSeq<T>>>,
        workers:    Vec<Sender<Message<T>>>,
        incoming:   Receiver<Message<T>>,
        poll_delay: Option<usize>) -> JoinHandle<()> {

        let worker = Worker { id, master, workers, incoming, poll_delay };
        thread::spawn(move || worker.run())
    }

    /// Recursively search for a tree-child sequence
    fn run(self) {
        while self.run_search() {}
    }

    /// Run a search and send the result back to the master
    fn run_search(&self) -> bool {

        if let Some(mut search) = self.get_work() {

            // Terminate the search immediately if it has no chance of success (too many non-trivial
            // cherries)
            let (keep_alive, seq) = if search.can_succeed() {

                // Create a new branch point for the current state
                search.start_branch();

                let keep_alive = match self.poll_delay {
                    Some(poll_delay) => self.run_search_cooperatively(&mut search, poll_delay),
                    None             => self.run_search_alone(&mut search),
                };

                // Return the tree-child sequence if we found one
                (keep_alive, search.tc_seq())

            } else {

                (true, None)
            };

            if let Some(seq) = seq {
                self.send_result(seq);
                false
            } else {
                keep_alive
            }
        } else {

            false
        }
    }

    /// Run the search without interacting with other workers
    fn run_search_alone(&self, search: &mut Search<T>) -> bool {
        while search.branch() {}
        true
    }

    /// Run the search in cooperation with other threads
    fn run_search_cooperatively(&self, search: &mut Search<T>, poll_delay: usize) -> bool {

        loop {

            // Run as many branching steps as indicated by poll_delay
            for _ in 0..poll_delay {
                if !search.branch() {
                    return true;
                }
            }

            // Check for incoming messages and respond to them
            if let Some(msg) = self.incoming_message() {
                match msg {
                    Message::Quit            => return false,
                    Message::GetWork(worker) => self.send_work(worker, Some(search)),
                    _                        => unreachable!(),
                }
            }
        }
    }

    /// Get the next piece of work to work on.  Returns `Some(Search<T>)` if we successfully
    /// received some work.  Returns `None` if no thread has any work, that is, everybody is idle.
    /// In this case, the search should be aborted.
    fn get_work(&self) -> Option<Search<T>> {

        self.incoming.set_state(false);

        let mut keep_trying = true;
        while keep_trying || self.id != 0 {

            // Check whether we should quit and either do so or yield the processor to other threads.
            if let Some(msg) = self.incoming_message() {
                match msg {
                    Message::Quit                   => return None,
                    Message::GetWork(worker)        => self.send_work(worker, None),
                    Message::SendWork(Some(search)) => return Some(search),
                    Message::SendWork(None)         => unreachable!(),
                }
            }
            yield_now();

            // Try to find a worker from whom we can steal work.  If we get a quit message in the
            // process, exit.
            keep_trying = false;
            for worker in self.workers.iter() {
                match worker.send_if(|| Message::GetWork(self.id), true) {
                    Status::FailState => {},
                    Status::FailFull  => keep_trying = true,
                    Status::Success   => match self.incoming.recv() {
                        Message::Quit => {
                            return None;
                        },
                        Message::GetWork(worker) => {
                            self.send_work(worker, None);
                        },
                        Message::SendWork(None) => {
                            keep_trying = true;
                        },
                        Message::SendWork(Some(mut search)) => {
                            if search.restrict_to_next_top_branch() {
                                self.incoming.set_state(true);
                                return Some(search);
                            } else {
                                keep_trying = true;
                            }
                        },
                    },
                }
            }
        }

        // If worker 0 does not find a worker to steal work from, it has to ask the master for more
        // work.
        self.master.send_drop(None);
        match self.incoming.recv() {
            Message::Quit => None,
            Message::SendWork(search) => {
                self.incoming.set_state(true);
                search
            },
            _ => unreachable!(),
        }
    }

    /// Send work to another worker
    fn send_work(&self, worker: usize, search: Option<&mut Search<T>>) {
        let success = {
            let package_search = || {
                let search_copy = match &search {
                    &None             => None,
                    &Some(ref search) => Some((*search).clone()),
                };
                Message::SendWork(search_copy)
            };
            self.workers[worker].send_if(package_search, false) == Status::Success
        };

        if success {
            search.map(|search| search.skip_next_top_branch());
        }
    }

    /// Send a result back to the master
    fn send_result(&self, seq: TcSeq<T>) {
        self.master.send_overwrite(Some(seq));
    }

    /// Check whether we have a message to process
    fn incoming_message(&self) -> Option<Message<T>> {
        self.incoming.try_recv()
    }
}

/// The type of message that can be sent to a worker
#[derive(Clone)]
pub enum Message<T> {

    /// Quit
    Quit,

    /// Request for work from another worker
    GetWork(usize),

    /// Send work to this worker.  This may be `None` so a worker can respond to a work request
    /// from another worker even if it itself has no work left to send to that other worker.
    SendWork(Option<Search<T>>),
}

#[cfg(test)]
mod tests {

    use super::super::channel::channel;
    use newick;
    use std::fmt::Write;
    use super::*;
    use tree::TreeBuilder;

    /// Test starting and stopping threads
    #[test]
    fn start_stop_workers() {

        const NUM_WORKERS: usize = 32;
        let (master_send,  _) = channel();
        let (worker_sends, worker_recvs): (Vec<Sender<Message<usize>>>, Vec<_>) =
            (0..NUM_WORKERS).map(|_| channel()).unzip();
        let worker_threads: Vec<_> = worker_recvs.into_iter().enumerate()
            .map(|(id, worker_recv)|
                 Worker::spawn(
                     id, master_send.clone(), worker_sends.clone(), worker_recv, Some(1)))
            .collect();

        for worker in worker_sends.iter() {
            worker.send_overwrite(Message::Quit);
        }

        for worker in worker_threads {
            worker.join().unwrap();
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

        let trees = {
            let mut builder = TreeBuilder::<String>::new();
            let newick = "((a,b),c);\n(a,(b,c));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };

        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();

        assert!(!search.success());

        const NUM_WORKERS: usize = 32;
        let (master_send,  master_recv) = channel();
        master_recv.set_state(true);
        let (worker_sends, worker_recvs): (Vec<Sender<Message<String>>>, Vec<_>) =
            (0..NUM_WORKERS).map(|_| channel()).unzip();
        let worker_threads: Vec<_> = worker_recvs.into_iter().enumerate()
            .map(|(id, worker_recv)|
                 Worker::spawn(
                     id, master_send.clone(), worker_sends.clone(), worker_recv, Some(1)))
            .collect();

        assert!(master_recv.recv().is_none());

        worker_sends[0].send_overwrite(Message::SendWork(Some(search)));

        assert!(master_recv.recv().is_none());

        for worker in worker_sends.iter() {
            worker.send_overwrite(Message::Quit);
        }

        for worker in worker_threads {
            worker.join().unwrap();
        }
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
        const NUM_WORKERS: usize = 32;
        let (master_send,  master_recv) = channel();
        master_recv.set_state(true);
        let (worker_sends, worker_recvs): (Vec<Sender<Message<String>>>, Vec<_>) =
            (0..NUM_WORKERS).map(|_| channel()).unzip();
        let worker_threads: Vec<_> = worker_recvs.into_iter().enumerate()
            .map(|(id, worker_recv)|
                 Worker::spawn(
                     id, master_send.clone(), worker_sends.clone(), worker_recv, Some(1)))
            .collect();

        assert!(master_recv.recv().is_none());

        worker_sends[0].send_overwrite(Message::SendWork(Some(search)));

        match master_recv.recv() {
            None => panic!("Expected tree-chlid sequence"),
            Some(seq) => {
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

            },
        }

        for worker in worker_sends.iter() {
            worker.send_overwrite(Message::Quit);
        }

        for worker in worker_threads {
            worker.join().unwrap();
        }
    }


    /// Test unsuccessful search with parameter 1
    #[test]
    fn search_1_fail() {

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
        const NUM_WORKERS: usize = 32;
        let (master_send,  master_recv) = channel();
        master_recv.set_state(true);
        let (worker_sends, worker_recvs): (Vec<Sender<Message<String>>>, Vec<_>) =
            (0..NUM_WORKERS).map(|_| channel()).unzip();
        let worker_threads: Vec<_> = worker_recvs.into_iter().enumerate()
            .map(|(id, worker_recv)|
                 Worker::spawn(
                     id, master_send.clone(), worker_sends.clone(), worker_recv, Some(1)))
            .collect();

        assert!(master_recv.recv().is_none());

        worker_sends[0].send_overwrite(Message::SendWork(Some(search)));

        assert!(master_recv.recv().is_none());

        for worker in worker_sends.iter() {
            worker.send_overwrite(Message::Quit);
        }

        for worker in worker_threads {
            worker.join().unwrap();
        }
    }

    /// Test successful search with parameter 2
    #[test]
    fn search_2_success() {

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
        const NUM_WORKERS: usize = 32;
        let (master_send,  master_recv) = channel();
        master_recv.set_state(true);
        let (worker_sends, worker_recvs): (Vec<Sender<Message<String>>>, Vec<_>) =
            (0..NUM_WORKERS).map(|_| channel()).unzip();
        let worker_threads: Vec<_> = worker_recvs.into_iter().enumerate()
            .map(|(id, worker_recv)|
                 Worker::spawn(
                     id, master_send.clone(), worker_sends.clone(), worker_recv, Some(1)))
            .collect();

        assert!(master_recv.recv().is_none());

        worker_sends[0].send_overwrite(Message::SendWork(Some(search)));

        match master_recv.recv() {
            None => panic!("Expected tree-chlid sequence"),
            Some(seq) => {
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

                println!("{}", string);
                assert!(
                    ["<(d, c), (d, e), (b, c), (b, a), (c, e), (a, e), (e, -)>",
                     "<(d, e), (d, c), (b, c), (b, a), (c, e), (a, e), (e, -)>",
                     "<(b, a), (d, e), (d, c), (b, c), (c, e), (a, e), (e, -)>",
                    ].contains(&&string[..]));
            },
        }

        for worker in worker_sends.iter() {
            worker.send_overwrite(Message::Quit);
        }

        for worker in worker_threads {
            worker.join().unwrap();
        }
    }
}
