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

use super::TcSeq;
use super::channel::{channel, Receiver, Sender};
use super::search::Search;
use super::worker::{Message, Worker};
use std::clone::Clone;
use std::mem;
use std::thread::JoinHandle;

/// The master thread
pub struct Master<T> {

    /// The problem instance to be solved
    search: Search<T>,

    /// The list of workers controlled by this master
    worker_threads: Vec<JoinHandle<()>>,

    /// The receiving end of the master channel
    incoming: Receiver<Option<TcSeq<T>>>,

    /// The message queues for the workers
    workers: Vec<Sender<Message<T>>>,
}

impl<T: Clone + Send + 'static> Master<T> {

    /// Run the master
    ///
    /// - `search` the search state to use as the start of the search
    /// - `num_workers` is the number of worker threads to be used for parallelizing the search
    /// - `poll_delay` is the number of branching steps a worker should complete before checking
    ///   for idle threads to share work with
    pub fn run(search: Search<T>, num_workers: usize, poll_delay: Option<usize>) -> Option<TcSeq<T>> {

        let mut master = Self::new(search, num_workers, poll_delay);

        loop {
            if let Some(seq) = master.result() {
                master.stop_workers();
                return Some(seq);
            }
            if !master.start_new_search() {
                master.stop_workers();
                return None
            }
        }
    }

    /// Create a new Master
    fn new(search: Search<T>, num_workers: usize, poll_delay: Option<usize>) -> Self {

        let (master_send,  master_recv) = channel();
        let (worker_sends, worker_recvs): (Vec<_>, Vec<_>) =
            (0..num_workers).map(|_| channel()).unzip();
        let worker_threads =
            worker_recvs.into_iter().enumerate()
            .map(|(id, worker_recv)|
                 Worker::spawn(
                     id, master_send.clone(), worker_sends.clone(), worker_recv, poll_delay))
            .collect();

        Master { search, worker_threads, incoming: master_recv, workers: worker_sends }
    }

    /// Start a new search.
    fn start_new_search(&mut self) -> bool {
        if self.search.increase_max_weight() {
            self.workers[0].send_overwrite(Message::SendWork(Some(self.search.clone())));
            true
        } else {
            false
        }
    }

    /// Wait for the result of the current search
    fn result(&self) -> Option<TcSeq<T>> {
        self.incoming.recv()
    }

    /// Stop all workers
    fn stop_workers(&mut self) {
        let workers        = mem::replace(&mut self.workers, vec![]);
        let worker_threads = mem::replace(&mut self.worker_threads, vec![]);

        for worker in workers {
            worker.send_overwrite(Message::Quit);
        }

        for worker in worker_threads {
            worker.join().unwrap();
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
            let newick =
                "(a,((b,(c,d)),e));\n((a,b),((c,d),e));\n((a,b),(c,(d,e)));\n(a,((b,c),(d,e)));\n";
            newick::parse_forest(&mut builder, newick).unwrap();
            builder.trees()
        };

        let mut search = Search::new(trees, true, true);
        search.resolve_trivial_cherries();

        let seq = Master::run(search, 32, Some(1));

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
