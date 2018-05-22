//! This module implements cluster partitioning for a collection of trees.  This implementation
//! does not work with the leaf labels directly to find matching leaves in different trees.
//! Instead, it assumes that the leaf IDs, which are unique integers in [0,n-1] for each tree, are
//! chosen so that the leaves with the same labels in different trees have the same integer ID.


use std::default::Default;
use tree::{Node, NodeData, Tree};
//use tree_child_sequence::{Pair, TcSeq};


/// The type used to represent clusters in the cluster partition
#[derive(Clone, Copy)]
pub struct Cluster(usize);


/// Type used to distinguish between leaves that are original leaves and leaves that represent
/// clusters produced by the cluster partition.
pub enum LoC<T> {

    /// An original leaf
    Leaf(T),

    /// A leaf representing a cluster
    Cluster(Cluster),
}


/// Partition the input trees into clusters.  In the output, the clusters are arranged bottom-up,
/// that is, the cluster containing the leaf representing another cluster C follows C in the
/// cluster sequence.
pub fn partition<T>(trees: Vec<Tree<T>>) -> Vec<Vec<Tree<LoC<T>>>> {

    // Compute an interval labelling for every tree and pair each tree with its labelling
    let intervals = trees.iter().map(leaf_intervals);
    let numbered_trees = trees.iter().zip(intervals).collect::<Vec<(&Tree<T>, Vec<(usize, usize)>)>>();

    // Map nodes of the first tree to the LCAs of their descendant leaves in all other trees and
    // vice versa.
    let forward_maps = numbered_trees[1..].iter()
        .map(|t| map_to_lca(&numbered_trees[0], t)).collect::<Vec<Vec<Node>>>();
    let backward_maps = numbered_trees[1..].iter()
        .map(|t| map_to_lca(t, &numbered_trees[0])).collect::<Vec<Vec<Node>>>();

    // Decompose the trees into clusters
    decompose_trees(&trees, forward_maps, backward_maps)
}


/// Number the leaves in `tree` left to right and label every node with the interval of numbers of
/// its descendant leaves.
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
            
            // The number of a leaf is the next available number
            NodeData::Leaf(_) => {
                self.intervals[node.id()] = (self.count, self.count);
                self.count += 1;
            },

            // The interval of an internal node starts at the number given to its first
            // descendant child and ends at the number given to its last descendant child.
            NodeData::Internal(ref data) => {
                let start = self.count;
                for child in self.tree.children(data) {
                    self.traverse(child);
                }
                self.intervals[node.id()] = (start, self.count - 1);
            },
        }
    }
}


/// Map every node in tree t1 to the LCA of its descendant leaves in t2
fn map_to_lca<T>(t1: &(&Tree<T>, Vec<(usize, usize)>), t2: &(&Tree<T>, Vec<(usize, usize)>)) -> Vec<Node> {
    LcaMapper::new(t1, t2).run()
}


/// The status of the LCA mapping process
struct LcaMapper<'a, T: 'a> {

    /// The tree to be mapped
    tree: &'a Tree<T>,

    /// Mapping from nodes to their parents in the tree to be mapped to.  (Extracted from the tree
    /// because the mapping process shortcuts these pointers to guarantee linear time.)
    parents: Vec<Option<Node>>,

    /// The leaf intervals associated with the nodes in the second tree.
    intervals: &'a Vec<(usize, usize)>,

    /// The constructed mapping
    mapping: Vec<Node>,
}


impl<'a, T: 'a> LcaMapper<'a, T> {

    /// Create a new `LcaMapper` for a pair of trees whose nodes have been numbered with leaf
    /// intervals.
    fn new(t1: &'a (&Tree<T>, Vec<(usize, usize)>), t2: &'a (&Tree<T>, Vec<(usize, usize)>)) -> LcaMapper<'a, T> {

        // Set up the initial mapping between matching leaves
        let mut mapping = vec![Default::default(); t1.0.node_count()];
        for leaf in t1.0.leaves() {
            mapping[t1.0[leaf.id()].id()] = t2.0[leaf.id()];
        }

        // Return the initial mapper state
        LcaMapper {
            tree:      t1.0,
            parents:   t2.0.nodes().map(|node| node.parent()).collect::<Vec<Option<Node>>>(),
            intervals: &t2.1,
            mapping,
        }
    }

    /// Run the LCA mapper
    fn run(mut self) -> Vec<Node> {
        self.traverse(self.tree.root().unwrap());
        self.mapping
    }

    /// Traverse the subtree of `self.t1` rooted in the given node and map all nodes in the subtree
    /// to corresponding nodes in `self.t2`.
    fn traverse(&mut self, node: Node) -> Node {

        // Leaves are already mapped, so deal only with internal nodes
        if let NodeData::Internal(ref data) = self.tree[node] {

            // Get the first candidate image as the image computed for the first child
            let mut children = self.tree.children(data);
            let first_buddy = self.traverse(children.next().unwrap());

            // Move the image up the tree to encompass the images of all the other children
            let mut buddy = first_buddy;
            for child in children {
                let interval = self.intervals[self.traverse(child).id()];
                while !contains(self.intervals[buddy.id()], interval) {
                    buddy = self.parents[buddy.id()].unwrap();
                }
            }

            // Shortcut the parent pointers on the traversed path so subsequent searches that hit
            // this path jump right up to its top
            let mut on_path = first_buddy;
            while on_path != buddy {
                self.parents[on_path.id()] = Some(buddy);
            }

            // Store the computed image of the current node
            self.mapping[node.id()] = buddy;
        }

        self.mapping[node.id()]
    }
}


/// Checks whether one interval contains another
fn contains(i1: (usize, usize), i2: (usize, usize)) -> bool {
    i1.0 <= i2.0 && i1.1 >= i2.1
}


/// Decompose the trees into clusters based on LCA mappings between the first tree and the other
/// trees
fn decompose_trees<T>(
    trees:         &Vec<Tree<T>>,
    forward_maps:  Vec<Vec<Node>>,
    backward_maps: Vec<Vec<Node>>) -> Vec<Vec<Tree<LoC<T>>>> {
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
