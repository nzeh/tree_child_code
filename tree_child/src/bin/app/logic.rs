//! This module implements the application logic of `tc_seq`, that is, the code that pulls together
//! the algorithms for computing a tree-child sequence and for computing a cluster partition, in
//! order to compute the final result.

use app;
use tree_child::clusters;
use tree_child::network::TcNet;
use tree_child::tree::Tree;
use tree_child::tree_child_sequence as tc;
use tree_child::tree_child_sequence::TcSeq;

/// The result of the tree-child sequence/network computation
pub enum TcResult {
    /// The result is a network
    Net(TcNet<String>),

    /// The result is a sequence
    Seq(TcSeq<String>),
}

/// Compute a tree-child sequence or network
pub fn tree_child_sequence_or_network(
    cfg: &app::Config,
    trees: Vec<Tree<String>>,
) -> app::Result<TcResult> {
    let tc_seq = if cfg.use_clustering {
        clusters::partition(trees)
            .into_iter()
            .map(|trees| tc_seq(cfg, trees))
            .collect::<Option<Vec<_>>>()
            .map(|cluster_seqs| clusters::combine_tc_seqs(cluster_seqs))
    } else {
        tc_seq(cfg, trees)
    };

    match (tc_seq, cfg.compute_network) {
        (Some(tc_seq), true) => Ok(TcResult::Net(TcNet::from_seq(tc_seq))),
        (Some(tc_seq), false) => Ok(TcResult::Seq(tc_seq)),
        (None, _) => Err(app::Error::Fail),
    }
}

/// Wrapper that call `tc::tree_child_sequence()` with the right arguments extracted from `cfg`
fn tc_seq<T: Clone + Send + 'static>(
    cfg: &app::Config,
    trees: Vec<Tree<T>>,
) -> Option<tc::TcSeq<T>> {
    tc::tree_child_sequence(
        trees,
        cfg.num_threads,
        cfg.poll_delay,
        cfg.limit_fanout,
        cfg.use_redundant_branch_opt,
        cfg.binary,
    )
}
