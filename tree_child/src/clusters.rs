//! This module implements cluster partitioning for a collection of trees with the same label set
//! `[0..n-1]`.


use std::mem;
use tree::{Info, Node, Tree};
//use tree_child_sequence::{Pair, TcSeq};


/// The type used to represent clusters in cluster partition
#[derive(Clone, Copy)]
pub struct Cluster(usize);


/// Type used to distinguish between leaves that are original leaves and leaves that represent
/// clusters produced by the cluster partition.
pub enum Loc<T> {

    /// An original leaf
    Node(T),

    /// A leaf representing a cluster
    Cluster(Cluster),
}


/// Partition the input trees into clusters.  In the output, the clusters are arranged bottom-up,
/// that is, the cluster containing the leaf representing another cluster C follows C in the
/// cluster sequence.
pub fn partition<T>(trees: Vec<Tree<T>>) -> Vec<Vec<Tree<Loc<T>>>> {

    // Compute an interval labelling for every tree and pair each tree with its labelling
    let preorder_numbers = trees.iter().map(leaf_intervals);
    let numbered_trees = trees.iter().zip(preorder_numbers).collect::<Vec<(&Tree<T>, Vec<(usize, usize)>)>>();

    // Map nodes of the first tree to the LCAs of their descendant leaves in all other trees and
    // vice versa.
    let forward_maps = numbered_trees[1..].iter()
        .map(|t| map_to_lca(&numbered_trees[0], t)).collect::<Vec<Vec<usize>>>();
    let backward_maps = numbered_trees[1..].iter()
        .map(|t| map_to_lca(t, &numbered_trees[0])).collect::<Vec<Vec<usize>>>();

    // Decompose the trees into clusters
    decompose_trees(&trees, forward_maps, backward_maps)
}


/// Number the leaves in `t` left to right and label every node with the interval of numbers
/// of its descendant leaves.
fn leaf_intervals<T>(tree: &Tree<T>) -> Vec<(usize, usize)> {
    LeafLabeller::new(tree).run()
}


/// The status of the leaf labelling process
struct LeafLabeller<'a, T: 'a> {
    tree:      &'a Tree<T>,
    count:     usize,
    intervals: Vec<(usize, usize)>,
}


impl<'a, T: 'a> LeafLabeller<'a, T> {
    
    /// Create a new `LeafLabeller` for the given tree
    fn new(tree: &Tree<T>) -> LeafLabeller<T> {
        LeafLabeller {
            tree,
            count:     0,
            intervals: vec![(0, 0); tree.node_count()],
        }
    }

    /// Run the labeller and return the resulting vector of intervals
    fn run(mut self) -> Vec<(usize, usize)> {
        self.traverse(self.tree.root().unwrap());
        self.intervals
    }

    /// Traverse the subtree rooted at the given node to compute the intervals of the nodes in this
    /// subtree
    fn traverse(&mut self, node: Node) {
        match self.tree[node] {
            
            Info::Leaf(_) => {
                self.intervals[node.id()] = (self.count, self.count);
                self.count += 1;
            },

            Info::Internal(ref info) => {
                let start = self.count;
                for child in self.tree.children(info) {
                    self.traverse(child);
                }
                self.intervals[node.id()] = (start, self.count - 1);
            },
        }
    }
}


/// Map every node in tree t1 to the LCA of its descendant leaves in t2
fn map_to_lca<T>(t1: &(&Tree<T>, Vec<(usize, usize)>), t2: &(&Tree<T>, Vec<(usize, usize)>)) -> Vec<usize> {
    let mapping = vec![0; t1.0.node_count()];
    // TODO: Finish this
    mapping
}

/// Decompose the trees into clusters based on LCA mappings between the first tree and the other
/// trees
fn decompose_trees<T>(
    trees:         &Vec<Tree<T>>,
    forward_maps:  Vec<Vec<usize>>,
    backward_maps: Vec<Vec<usize>>) -> Vec<Vec<Tree<Loc<T>>>> {
    vec![]
}


///// Assemble the tree-child sequence of the original input from tree-child sequences constructed
///// for individual clusters.  This assumes that the tree-child sequences are arranged in the same
///// order as in the output of `partition()`.
//pub fn combine_tc_seqs<T>(tc_seqs: Vec<TcSeq<Loc<T>>>) -> TcSeq<T> {
//
//    // The last leaf remaining in each tree-child sequence
//    let mut last_leaves = vec![0; tc_seqs.len()];
//
//    // Initialize the last leaves
//    for (i, tc_seq) in &tc_seqs.iter().enumerate() {
//        let Pair::Final(leaf) = tc_seq[tc_seq.len() - 1];
//        match leaf {
//            Loc::Node(l)    => last_leaves[i] = l,
//            Loc::Cluster(c) => last_leaves[i] = last_leaves[c],
//        }
//    }
//
//    // The combined sequence
//    let combined_seq = Vec::with_capacity(usize::sum(&tc_seqs.iter().map(|seq| seq.len() - 1)) + 1);
//
//    // Build the combined sequence
//    for tc_seq in &tc_seqs.iter() {
//        for pair in tc_seq[..tc_seq.len() - 1] {
//            if let Pair::Reduce(x, y) = pair {
//                let x_ = match x {
//                    Loc::Node(l)    => l,
//                    Loc::Cluster(c) => last_leaves[c],
//                };
//                let y_ = match y {
//                    Loc::Node(l)    => l,
//                    Loc::Cluster(c) => last_leaves[c],
//                };
//                combined_seq.push(Pair::Reduce(x_, y_));
//            }
//        }
//    }
//
//    // Add the final leaf
//    let tc_seq = tc_seqs[tc_seqs.len() - 1];
//    if let Pair::Final(leaf) = tc_seq[tc_seq.len() - 1] {
//        combined_seq.push(match leaf {
//            Loc::Node(l)    => l,
//            Loc::Cluster(c) => last_leaves[c],
//        });
//    }
//
//    combined_seq
//}
