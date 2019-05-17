//! This module implements the application logic of `tc_seq`, that is, the code that pulls together
//! the algorithms for computing a tree-child sequence and for computing a cluster partition, in
//! order to compute the final result.

use app;
use clusters;
use network::TcNet;
use tree::Tree;
use tree_child_sequence as tc;
use tree_child_sequence::TcSeq;

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
        clusters::combine_tc_seqs(
            clusters::partition(trees)
                .into_iter()
                .map(|trees| tc_seq(cfg, trees))
                .collect::<app::Result<Vec<_>>>()?,
        )
    } else {
        tc_seq(cfg, trees)?
    };

    Ok(if cfg.compute_network {
        TcResult::Net(TcNet::from_seq(tc_seq))
    } else {
        TcResult::Seq(tc_seq)
    })
}

/// Wrapper that call `tc::tree_child_sequence()` with the right arguments extracted from `cfg`
fn tc_seq<T: Clone + Send + 'static>(
    cfg: &app::Config,
    trees: Vec<Tree<T>>,
) -> app::Result<tc::TcSeq<T>> {
    tc::tree_child_sequence(
        trees,
        cfg.num_threads,
        cfg.poll_delay,
        cfg.limit_fanout,
        cfg.use_redundant_branch_opt,
        cfg.binary,
    )
}
