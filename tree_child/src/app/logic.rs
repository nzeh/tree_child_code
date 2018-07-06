//! This module implements the application logic of `tc_seq`, that is, the code that pulls together
//! the algorithms for computing a tree-child sequence and for computing a cluster partition, in
//! order to compute the final result.

use app;
use clusters;
use tree::Tree;
use tree_child_sequence as tc;

/// Compute a tree-child sequence
pub fn tree_child_sequence(cfg: &app::Config, trees: Vec<Tree<String>>) -> tc::TcSeq<String> {
    if cfg.use_clustering {
        clusters::combine_tc_seqs(
            clusters::partition(trees)
                .into_iter()
                .map(|trees| tc_seq(cfg, trees))
                .collect())
    } else {
        tc_seq(cfg, trees)
    }
}

/// Wrapper that call `tc::tree_child_sequence()` with the right arguments extracted from `cfg`
fn tc_seq<T: Clone + Send + 'static>(cfg: &app::Config, trees: Vec<Tree<T>>) -> tc::TcSeq<T> {
        tc::tree_child_sequence(trees,
                                cfg.num_threads, cfg.poll_delay, cfg.limit_fanout,
                                cfg.use_redundant_branch_opt)
}
