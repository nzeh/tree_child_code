//! This module implements cluster partitioning for a collection of trees.  This implementation
//! does not work with the leaf labels directly to find matching leaves in different trees.
//! Instead, it assumes that the leaf IDs, which are unique integers in [0,n-1] for each tree, are
//! chosen so that the leaves with the same labels in different trees have the same integer ID.


use std::default::Default;
use std::marker::PhantomData;
use tree::traits::{Id, Tree, TreeBuilder};
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
pub fn partition<Label, T, C, B>(trees: Vec<T>) -> Vec<Vec<C>>
    where for<'a> Label: 'a,
          for<'a> T:     'a + Tree<'a, Label>,
          for<'a> C:     'a + Tree<'a, LoC<Label>>,
          for<'a> B:     'a + TreeBuilder<'a, LoC<Label>, Tree=C> {

    let (num_clusters, cluster_nodes) = {

        // Compute an interval labelling for every tree and pair each tree with its labelling
        let intervals = trees.iter().map(leaf_intervals);
        let numbered_trees = trees.iter().zip(intervals).collect::<Vec<(&T, Vec<(usize, usize)>)>>();

        // Map nodes of the first tree to the LCAs of their descendant leaves in all other trees
        // and vice versa.
        let forward_maps = numbered_trees[1..].iter()
            .map(|t| map_to_lca(&numbered_trees[0], t)).collect();
        let backward_maps = numbered_trees[1..].iter()
            .map(|t| map_to_lca(t, &numbered_trees[0])).collect();

        // Identify nodes that are clusters
        identify_clusters(&trees[0], forward_maps, backward_maps)
    };

    // Decompose the trees into clusters
    decompose_trees::<Label, T, C, B>(trees, num_clusters, cluster_nodes)
}


/// Number the leaves in `tree` left to right and label every node with the interval of numbers of
/// its descendant leaves.
fn leaf_intervals<'a, Label, T>(tree: &'a T) -> Vec<(usize, usize)>
    where Label: 'a,
          T:     'a + Tree<'a, Label> {
    LeafLabeller::new(tree).run()
}


/// The status of the leaf labelling process
struct LeafLabeller<'a, Label, T>
    where Label: 'a,
          T:     'a + Tree<'a, Label> {
    tree:       &'a T,
    next_label: usize,
    intervals:  Vec<(usize, usize)>,
    phantom:    PhantomData<&'a Label>,
}


impl<'a, Label, T> LeafLabeller<'a, Label, T>
    where T: Tree<'a, Label> {
    
    /// Create a new `LeafLabeller` for the given tree
    fn new(tree: &'a T) -> Self {
        LeafLabeller {
            tree,
            next_label: 0,
            intervals:  vec![Default::default(); tree.node_count()],
            phantom:    PhantomData,
        }
    }

    /// Run the labeller and return the resulting vector of intervals
    fn run(mut self) -> Vec<(usize, usize)> {
        self.traverse(self.tree.root().unwrap());
        self.intervals
    }

    /// Traverse the subtree rooted at the given node to compute the intervals of the nodes in this
    /// subtree
    fn traverse(&mut self, node: T::Node) {

        if self.tree.is_leaf(node) {

            // The number of a leaf is the next available number
            self.intervals[node.id()] = (self.next_label, self.next_label);
            self.next_label += 1;

        } else {

            // The interval of an internal node starts at the number given to its first descendant
            // child and ends at the number given to its last descendant child.
            let min_label = self.next_label;
            for child in self.tree.children(node) {
                self.traverse(child);
            }
            self.intervals[node.id()] = (min_label, self.next_label - 1);
        }
    }
}


/// Map every node in tree t1 to the LCA of its descendant leaves in t2
fn map_to_lca<'a, Label, T>(
    t1: &'a (&'a T, Vec<(usize, usize)>),
    t2: &'a (&'a T, Vec<(usize, usize)>)) -> Vec<T::Node>
    where Label: 'a,
          T:     'a + Tree<'a, Label> {
    LcaMapper::new(t1, t2).run()
}


/// The status of the LCA mapping process
struct LcaMapper<'a, Label, T>
    where Label: 'a,
          T:     'a + Tree<'a, Label> {

    /// The tree to be mapped
    tree: &'a T,

    /// Mapping from nodes to their parents in the tree to be mapped to.  (Extracted from the tree
    /// because the mapping process shortcuts these pointers to guarantee linear time.)
    parents: Vec<Option<T::Node>>,

    /// The leaf intervals associated with the nodes in the second tree.
    intervals: &'a Vec<(usize, usize)>,

    /// The constructed mapping
    mapping: Vec<T::Node>,
}


impl<'a, Label, T> LcaMapper<'a, Label, T>
    where Label: 'a,
          T:     'a + Tree<'a, Label> {

    /// Create a new `LcaMapper` for a pair of trees whose nodes have been numbered with leaf
    /// intervals.
    fn new(t1: &'a (&'a T, Vec<(usize, usize)>),
           t2: &'a (&'a T, Vec<(usize, usize)>)) -> Self {

        // Set up the initial mapping between matching leaves
        let mut mapping = vec![T::Node::new(0); t1.0.node_count()];
        for leaf in t1.0.leaves() {
            mapping[leaf.id()] = t2.0.leaf(t1.0.leaf_id(leaf).unwrap());
        }

        // Return the initial mapper state
        LcaMapper {
            tree:      t1.0,
            parents:   t2.0.nodes().map(|node| t1.0.parent(node)).collect(),
            intervals: &t2.1,
            mapping,
        }
    }

    /// Run the LCA mapper
    fn run(mut self) -> Vec<T::Node> {
        self.traverse(self.tree.root().unwrap());
        self.mapping
    }

    /// Traverse the subtree of `self.t1` rooted in the given node and map all nodes in the subtree
    /// to corresponding nodes in `self.t2`.
    fn traverse(&mut self, node: T::Node) -> T::Node {

        if !self.tree.is_leaf(node) {

            // Get the first candidate image as the image computed for the first child
            let mut children = self.tree.children(node);
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
                let next_on_path = self.parents[on_path.id()].unwrap();
                self.parents[on_path.id()] = Some(buddy);
                on_path = next_on_path;
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


/// Identify all nodes that are roots of clusters
fn identify_clusters<'a, Label, T>(
    tree:          &'a T,
    forward_maps:  Vec<Vec<T::Node>>,
    backward_maps: Vec<Vec<T::Node>>) -> (usize, Vec<Vec<Option<usize>>>)
    where Label: 'a,
          T:     'a + Tree<'a, Label> {

    let mut cluster_nodes = vec![vec![None; forward_maps[0].len()]; forward_maps.len() + 1];
    let mut cluster_id = 0;
    'l: for node in 0..forward_maps[0].len() {
        if tree.is_leaf(T::Node::new(node)) {
            continue 'l
        }
        for t in 0..forward_maps.len() {
            if backward_maps[t][forward_maps[t][node].id()].id() != node {
                continue 'l
            }
        }
        cluster_nodes[0][node] = Some(cluster_id);
        for t in 0..forward_maps.len() {
            cluster_nodes[t+1][forward_maps[t][node].id()] = Some(cluster_id);
        }
        cluster_id += 1;
    }
    (cluster_id, cluster_nodes)
}


/// Decompose the trees into clusters based on LCA mappings between the first tree and the other
/// trees
fn decompose_trees<Label, T, C, B>(
    trees:         Vec<T>,
    num_clusters:  usize,
    cluster_nodes: Vec<Vec<Option<usize>>>) -> Vec<Vec<C>>
    where for<'a> Label: 'a,
          for<'a> T:     'a + Tree<'a, Label>,
          for<'a> C:     'a + Tree<'a, LoC<Label>>,
          for<'a> B:     'a + TreeBuilder<'a, LoC<Label>, Tree=C> {

    let mut decomp = Decomposer::new(num_clusters);
    for (t, cs) in trees.into_iter().zip(cluster_nodes) {
        decomp.run(t, cs);
    }
    decomp.clusters()
}


/// The state of the cluster decomposition process
struct Decomposer<'a, Label, T, C, B>
    where Label: 'a,
          T:     'a + Tree<'a, Label>,
          C:     'a + Tree<'a, LoC<Label>>,
          B:     'a + TreeBuilder<'a, LoC<Label>, Tree=C> {

    /// Tree builders used to build the trees in the different clusters
    builders: Vec<B>,

    /// The current tree
    tree: T,

    /// The cluster nodes of the current tree
    cluster_nodes: Vec<Option<usize>>,

    phantom: PhantomData<&'a Label>,
}


impl<'a, Label, TNode, CNode, T, C, B> Decomposer<'a, Label, T, C, B>
    where Label: 'a,
          TNode: Clone + Copy + Id + PartialEq,
          CNode: Clone + Copy + Id + PartialEq,
          T:     'a + Tree<'a, Label, Node=TNode>,
          C:     'a + Tree<'a, LoC<Label>, Node=CNode>,
          B:     'a + TreeBuilder<'a, LoC<Label>, Tree=C> {

    /// Construct a new decomposer capable of building num_clusters + 1 clusters
    fn new(num_clusters: usize) -> Self {
        let mut builders = vec![];
        for _ in 0..num_clusters + 1 {
            builders.push(B::new());
        }
        Decomposer {
            builders,
            tree:          T::new(),
            cluster_nodes: vec![],
        }
    }

    /// Decompose tree into its clusters
    fn run(&mut self, tree: T, cluster_nodes: Vec<Option<usize>>) {
        self.tree = tree;
        self.cluster_nodes = cluster_nodes;
        let root = self.tree.root().unwrap();
        self.traverse(root, None);
    }

    /// Traverse the tree from the given node
    fn traverse(&mut self, node: TNode, cluster: Option<usize>) -> CNode {

        if self.tree.is_leaf(node) {

            self.builders[cluster.unwrap()].new_leaf(LoC::Leaf(self.tree.label(node)))

        } else if let Some(c) = self.cluster_nodes[node.id()] {

            // Build the cluster rooted in this node
            self.builders[c].new_tree();
            let children = self.tree.children(node)
                .map(|child| self.traverse(child, Some(c)))
                .collect();
            let root = self.builders[c].new_node(children);
            self.builders[c].finish_tree(root);

            // Return a leaf to be added to the parent cluster
            match cluster {
                Some(c0) => self.builders[c0].new_leaf(LoC::Cluster(Cluster(c))),
                _        => Default::default(),
            }

        } else {

            let children = self.tree.children(node)
                .map(|child| self.traverse(child, cluster))
                .collect();
            self.builders[cluster.unwrap()].new_node(children)

        }
    }

    /// Collect the clusters constructed by the decomposer
    fn clusters(self) -> Vec<Vec<C>> {
        self.builders.into_iter().map(|b| b.trees()).collect()
    }
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
