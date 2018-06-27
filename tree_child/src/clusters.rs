//! This module implements cluster partitioning for a collection of trees.  It decomposes a
//! collection of trees into a collection of clusters and allows the tree-child sequences
//! of the clusters to be combined into a tree-child sequence for the whole input.
//!
//! This implementation does not work with the leaf labels directly to find matching leaves in
//! different trees.  Instead, it assumes that the leaf IDs, which are unique integers in [0,n-1]
//! for each tree, are chosen so that the leaves with the same labels in different trees have the
//! same integer ID.
//!
//! Two methods are provided:
//!
//! `partition()` takes a vector of trees and returns a vector of vectors of trees.  Each inner
//! vector represents a cluster.
//!
//! `combine_tc_seqs()` takes the tree-child sequences computed for the clusters and stitches
//! them together to obtain a tree-child sequence for the original input.  For this to work
//! correctly, the tree-child sequences must be given in the same order as the corresponding
//! clusters output by `partition()`.


use std::default::Default;
use std::hash::Hash;
use tree::{Node, Tree, TreeBuilder};
//use tree_child_sequence::{Pair, TcSeq};


/// The type used to represent clusters in the cluster partition
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct Cluster(usize);


/// Type used to distinguish between leaves that are original leaves and leaves that represent
/// clusters produced by the cluster partition.
#[derive(Clone, Eq, Hash, PartialEq)]
pub enum LoC<T> {

    /// An original leaf
    Leaf(T),

    /// A leaf representing a cluster
    Cluster(Cluster),
}


/// Partition the input trees into clusters.  In the output, the clusters are arranged bottom-up,
/// that is, the cluster containing the leaf representing another cluster C follows C in the
/// cluster sequence.
///
/// The input trees may be multifurcating, but the cluster partition is not as good as it could be
/// in this case because the cluster partition looks only for "hard" clusters (nodes with the
/// same set of descendant leaves in all input trees).  Usually, one wants "soft" clusters (nodes
/// with the same set of descendant leaves in appropriate binary resolutions of the input trees).
///
/// # Example:
///
/// ```
/// # use tree_child::newick;
/// # use tree_child::tree;
/// # use tree_child::clusters::{LoC, partition};
/// let newick      = "((a,(b,(c,d))),e);\n(a,(((b,c),d),e));\n";
/// let mut builder = tree::TreeBuilder::new();
/// newick::parse_forest(&mut builder, newick).unwrap();
/// let trees    = builder.trees();
/// let clusters = partition(trees);
/// assert_eq!(clusters.len(), 2);
/// assert_eq!(clusters[0][0].leaf_count(), 3);
/// assert_eq!(clusters[0][1].leaf_count(), 3);
/// assert_eq!(clusters[1][0].leaf_count(), 3);
/// assert_eq!(clusters[1][1].leaf_count(), 3);
/// ```
pub fn partition<T: Clone + Eq + Hash>(trees: Vec<Tree<T>>) -> Vec<Vec<Tree<LoC<T>>>> {

    let (num_clusters, cluster_nodes) = {

        // Compute an interval labelling for every tree and pair each tree with its labelling
        let intervals = trees.iter().map(leaf_intervals);
        let numbered_trees: Vec<(&Tree<T>, Vec<(usize, usize)>)>
            = trees.iter().zip(intervals).collect();

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
    decompose_trees(trees, num_clusters, cluster_nodes)
}


/// Number the leaves in `tree` left to right and label every node with the interval of numbers of
/// its descendant leaves.
fn leaf_intervals<T: Clone>(tree: &Tree<T>) -> Vec<(usize, usize)> {
    LeafLabeller::new(tree).run()
}


/// The status of the leaf labelling process
struct LeafLabeller<'t, T: 't> {
    tree:       &'t Tree<T>,
    next_label: usize,
    intervals:  Vec<(usize, usize)>,
}


impl<'t, T: 't + Clone> LeafLabeller<'t, T> {
    
    /// Create a new `LeafLabeller` for the given tree
    fn new(tree: &'t Tree<T>) -> Self {
        LeafLabeller {
            tree,
            next_label: 0,
            intervals:  vec![Default::default(); tree.node_count()],
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
fn map_to_lca<T: Clone>(t1: &(&Tree<T>, Vec<(usize, usize)>),
                        t2: &(&Tree<T>, Vec<(usize, usize)>)) -> Vec<Node> {
    LcaMapper::new(t1, t2).run()
}


/// The status of the LCA mapping process
struct LcaMapper<'t, T: 't> {

    /// The tree to be mapped
    tree: &'t Tree<T>,

    /// Mapping from nodes to their parents in the tree to be mapped to.  (Extracted from the tree
    /// because the mapping process shortcuts these pointers to guarantee linear time.)
    parents: Vec<Option<Node>>,

    /// The leaf intervals associated with the nodes in the second tree.
    intervals: &'t Vec<(usize, usize)>,

    /// The constructed mapping
    mapping: Vec<Node>,
}


impl<'t, T: 't + Clone> LcaMapper<'t, T> {

    /// Create a new `LcaMapper` for a pair of trees whose nodes have been numbered with leaf
    /// intervals.
    fn new(t1: &'t (&'t Tree<T>, Vec<(usize, usize)>),
           t2: &'t (&'t Tree<T>, Vec<(usize, usize)>)) -> Self {

        // Set up the initial mapping between matching leaves
        let mut mapping = vec![Default::default(); t1.0.node_count()];
        for leaf in t1.0.leaves() {
            mapping[leaf.id()] = t2.0.leaf(t1.0.leaf_id(leaf).unwrap());
        }

        // Return the initial mapper state
        LcaMapper {
            tree:      t1.0,
            parents:   t2.0.nodes().map(|node| t2.0.parent(node)).collect(),
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

        if !self.tree.is_leaf(node) {

            // Get the first candidate image as the image computed for the first child
            let mut children = self.tree.children(node);
            let first_buddy  = self.traverse(children.next().unwrap());

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
fn identify_clusters<T: Clone>(tree:          &Tree<T>,
                               forward_maps:  Vec<Vec<Node>>,
                               backward_maps: Vec<Vec<Node>>) -> (usize, Vec<Vec<Option<usize>>>) {

    let mut cluster_nodes = vec![];
    cluster_nodes.push(vec![None; forward_maps[0].len()]);
    for m in backward_maps.iter() {
        cluster_nodes.push(vec![None; m.len()]);
    }

    let mut cluster_id = 0;
    'l: for node in 0..forward_maps[0].len() {

        if tree.is_leaf(Node::new(node)) {
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
fn decompose_trees<T: Clone + Eq + Hash>(
    trees:         Vec<Tree<T>>,
    num_clusters:  usize,
    cluster_nodes: Vec<Vec<Option<usize>>>) -> Vec<Vec<Tree<LoC<T>>>> {

    let mut decomp = Decomposer::new(num_clusters);
    for (t, cs) in trees.into_iter().zip(cluster_nodes) {
        decomp.run(t, cs);
    }
    decomp.clusters()
}


/// The state of the cluster decomposition process
struct Decomposer<T> {

    /// Tree builders used to build the trees in the different clusters
    builders: Vec<TreeBuilder<LoC<T>>>,
}


impl<T: Clone + Eq + Hash> Decomposer<T> {

    /// Construct a new decomposer capable of building num_clusters + 1 clusters
    fn new(num_clusters: usize) -> Self {
        let mut builders = vec![];
        for _ in 0..num_clusters {
            builders.push(TreeBuilder::new());
        }
        Decomposer { builders }
    }

    /// Decompose tree into its clusters
    fn run(&mut self, tree: Tree<T>, cluster_nodes: Vec<Option<usize>>) {
        self.traverse(&tree, &cluster_nodes, tree.root().unwrap(), None);
    }

    /// Traverse the tree from the given node
    fn traverse(&mut self,
                tree:          &Tree<T>,
                cluster_nodes: &Vec<Option<usize>>,
                node:          Node,
                cluster:       Option<usize>) -> Node {

        if tree.is_leaf(node) {

            self.builders[cluster.unwrap()]
                .new_leaf(LoC::Leaf((*tree.label(node).unwrap()).clone()))

        } else if let Some(c) = cluster_nodes[node.id()] {

            // Build the cluster rooted in this node
            self.builders[c].new_tree();
            let children = tree.children(node)
                .map(|child| self.traverse(tree, cluster_nodes, child, Some(c))).collect();
            let root = self.builders[c].new_node(children);
            self.builders[c].finish_tree(root);

            // Return a leaf to be added to the parent cluster
            match cluster {
                Some(c0) => self.builders[c0].new_leaf(LoC::Cluster(Cluster(c))),
                _        => Default::default(),
            }

        } else {

            let children = tree.children(node)
                .map(|child| self.traverse(tree, cluster_nodes, child, cluster))
                .collect();
            self.builders[cluster.unwrap()].new_node(children)

        }
    }

    /// Collect the clusters constructed by the decomposer
    fn clusters(self) -> Vec<Vec<Tree<LoC<T>>>> {
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

#[cfg(test)]
mod tests {

    use super::*;
    use newick;

    /// Construct a forest to be used in subsequent tests
    fn build_forest() -> Vec<Tree<String>> {
        let mut builder  = TreeBuilder::<String>::new();
        let tree1_newick = "((a,((d,e),(((o,n),(l,m,p)),(f,(q,(r,s))),g))),(b,((h,i),(j,k)),c));";
        let tree2_newick = "((b,(k,(i,(j,h)))),(a,(d,(e,(((l,((m,n),(o,p))),(r,(s,q)),g),f))),c));";
        let tree3_newick = "((b,(k,(i,j),h)),((a,c),(((l,((o,n,p),m)),(f,(s,(q,r))),d),(e,g))));";
        let mut newick   = String::new();
        newick += tree1_newick;
        newick.push('\n');
        newick += tree2_newick;
        newick.push('\n');
        newick += tree3_newick;
        newick.push('\n');
        newick::parse_forest(&mut builder, &newick).unwrap();
        builder.trees()
    }

    /// Test that the leaf intervals are computed correctly
    #[test]
    fn test_leaf_intervals() {
        let trees                               = build_forest();
        let intervals: Vec<Vec<(usize, usize)>> = trees.iter().map(leaf_intervals).collect();
        assert_eq!(intervals[0],
                   vec![
                   (0,0),(1,1),(2,2),(1,2),(3,3),(4,4),(3,4),(5,5),(6,6),(7,7),(5,7),
                   (3,7),(8,8),(9,9),(10,10),(11,11),(10,11),(9,11),(8,11),(12,12),
                   (3,12),(1,12),(0,12),(13,13),(14,14),(15,15),(14,15),(16,16),(17,17),
                   (16,17),(14,17),(18,18),(13,18),(0,18)]);
        assert_eq!(intervals[1],
                   vec![
                   (0,0),(1,1),(2,2),(3,3),(4,4),(3,4),(2,4),(1,4),(0,4),
                   (5,5),(6,6),(7,7),(8,8),(9,9),(10,10),(9,10),(11,11),(12,12),(11,12),
                   (9,12),(8,12),(13,13),(14,14),(15,15),(14,15),(13,15),(16,16),(8,16),
                   (17,17),(8,17),(7,17),(6,17),(18,18),(5,18),(0,18)]);
        assert_eq!(intervals[2],
                   vec![
                   (0,0),(1,1),(2,2),(3,3),(2,3),(4,4),(1,4),(0,4),
                   (5,5),(6,6),(5,6),
                   (7,7),(8,8),(9,9),(10,10),(8,10),(11,11),(8,11),(7,11),
                   (12,12),(13,13),(14,14),(15,15),(14,15),(13,15),(12,15),(16,16),(7,16),
                   (17,17),(18,18),(17,18),(7,18),(5,18),(0,18)]);
    }

    /// Test that the LCA mapping is correct
    #[test]
    fn test_lca_mapping() {
        let trees     = build_forest();
        let intervals = trees.iter().map(leaf_intervals);
        let numbered_trees: Vec<(&Tree<String>, Vec<(usize, usize)>)>
            = trees.iter().zip(intervals).collect();
        let forward_maps: Vec<Vec<usize>> = numbered_trees[1..].iter()
            .map(|t| map_to_lca(&numbered_trees[0], t))
            .map(|m| m.into_iter().map(|node| node.id()).collect())
            .collect();
        let backward_maps: Vec<Vec<usize>> = numbered_trees[1..].iter()
            .map(|t| map_to_lca(t, &numbered_trees[0]))
            .map(|m| m.into_iter().map(|node| node.id()).collect())
            .collect();
        assert_eq!(forward_maps[0],
                   vec![
                   9,10,11,31,16,14,19,12,13,17,20,20,28,23,21,22,25,25,29,26,29,
                   31,33,0,4,2,6,3,1,7,7,32,34,34]);
        assert_eq!(forward_maps[1],
                   vec![
                   8,26,28,31,12,13,15,11,16,14,18,18,19,21,22,20,24,24,25,29,
                   31,31,32,0,5,2,6,3,1,6,6,9,33,33]);
        assert_eq!(backward_maps[0],
                   vec![
                   23,28,25,27,24,30,30,30,32,0,1,2,7,8,5,11,4,9,11,11,11,14,15,13,17,17,
                   19,20,12,20,21,21,31,33,33]);
        assert_eq!(backward_maps[1],
                   vec![
                   23,28,25,27,30,24,30,32,0,31,33,7,4,5,9,11,8,11,11,12,15,13,14,17,17,18,
                   1,21,2,19,21,21,33,33]);
    }

    /// Test that the clusters are identified correctly
    #[test]
    fn test_identify_clusters() {
        let trees = build_forest();
        let (num_clusters, cluster_nodes) = {
            let intervals = trees.iter().map(leaf_intervals);
            let numbered_trees: Vec<(&Tree<String>, Vec<(usize, usize)>)>
                = trees.iter().zip(intervals).collect();
            let forward_maps = numbered_trees[1..].iter()
                .map(|t| map_to_lca(&numbered_trees[0], t)).collect();
            let backward_maps = numbered_trees[1..].iter()
                .map(|t| map_to_lca(t, &numbered_trees[0])).collect();
            identify_clusters(&trees[0], forward_maps, backward_maps)
        };
        assert_eq!(num_clusters, 5);
        assert_eq!(cluster_nodes[0],
                   vec![
                   None, None, None, None, None, None, None, None, None, None, None,
                   Some(0), None, None, None, None, None, Some(1), None, None, None,
                   Some(2), None, None, None, None, None, None, None, None, Some(3),
                   None, None, Some(4)]);
        assert_eq!(cluster_nodes[1],
                   vec![
                   None, None, None, None, None, None, None, Some(3), None,
                   None, None, None, None, None, None, None, None, None, None, None, Some(0),
                   None, None, None, None, Some(1), None, None, None, None, None, Some(2),
                   None, None, Some(4)]);
        assert_eq!(cluster_nodes[2],
                   vec![
                   None, None, None, None, None, None, Some(3), None, None, None, None,
                   None, None, None, None, None, None, None, Some(0), None, None, None,
                   None, None, Some(1), None, None, None, None, None, None, Some(2),
                   None, Some(4)]);
    }

    /// Translate the labels of the trees in a cluster partition into string labels so they
    /// can be sent to format_forest
    fn with_string_labels(clusters: Vec<Vec<Tree<LoC<String>>>>) -> Vec<Vec<Tree<String>>> {

        fn translate_labels(
            builder: &mut TreeBuilder<String>,
            tree: &Tree<LoC<String>>,
            node: Node) -> Node {

            match tree.label(node) {

                Some(label) => {
                    match label {
                        LoC::Leaf(label)         => builder.new_leaf(label.clone()),
                        LoC::Cluster(Cluster(c)) => builder.new_leaf(format!("C{}", c)),
                    }
                },

                None => {
                    let children = tree.children(node).map(
                        |child| translate_labels(builder, tree, child)).collect();
                    builder.new_node(children)
                },
            }
        }

        let mut output_clusters = vec![];
        for cluster in clusters {
            let mut builder = TreeBuilder::<String>::new();
            for tree in cluster {
                builder.new_tree();
                let root = translate_labels(&mut builder, &tree, tree.root().unwrap());
                builder.finish_tree(root);
            }
            output_clusters.push(builder.trees());
        }
        output_clusters
    }

    /// Test that the trees are decomposed correctly
    #[test]
    fn test_decompose_trees() {
        let trees = build_forest();
        let (num_clusters, cluster_nodes) = {
            let intervals = trees.iter().map(leaf_intervals);
            let numbered_trees: Vec<(&Tree<String>, Vec<(usize, usize)>)>
                = trees.iter().zip(intervals).collect();
            let forward_maps = numbered_trees[1..].iter()
                .map(|t| map_to_lca(&numbered_trees[0], t)).collect();
            let backward_maps = numbered_trees[1..].iter()
                .map(|t| map_to_lca(t, &numbered_trees[0])).collect();
            identify_clusters(&trees[0], forward_maps, backward_maps)
        };
        let clusters =
            with_string_labels(decompose_trees(trees, num_clusters, cluster_nodes));
        assert_eq!(clusters.len(), 5);
        let expected_newicks = [
            "((o,n),(l,m,p));\n(l,((m,n),(o,p)));\n(l,((o,n,p),m));\n",
            "(q,(r,s));\n(r,(s,q));\n(s,(q,r));\n",
            "((d,e),(C0,(f,C1),g));\n(d,(e,((C0,C1,g),f)));\n((C0,(f,C1),d),(e,g));\n",
            "((h,i),(j,k));\n(k,(i,(j,h)));\n(k,(i,j),h);\n",
            "((a,C2),(b,C3,c));\n((b,C3),(a,C2,c));\n((b,C3),((a,c),C2));\n",
        ];
        for i in 0..clusters.len() {
            assert_eq!(newick::format_forest(&clusters[i]).unwrap(), expected_newicks[i]);
        }
    }

    /// Now test the whole package
    #[test]
    fn test_partition() {
        let trees = build_forest();
        let clusters = with_string_labels(partition(trees));
        assert_eq!(clusters.len(), 5);
        let expected_newicks = [
            "((o,n),(l,m,p));\n(l,((m,n),(o,p)));\n(l,((o,n,p),m));\n",
            "(q,(r,s));\n(r,(s,q));\n(s,(q,r));\n",
            "((d,e),(C0,(f,C1),g));\n(d,(e,((C0,C1,g),f)));\n((C0,(f,C1),d),(e,g));\n",
            "((h,i),(j,k));\n(k,(i,(j,h)));\n(k,(i,j),h);\n",
            "((a,C2),(b,C3,c));\n((b,C3),(a,C2,c));\n((b,C3),((a,c),C2));\n",
        ];
        for i in 0..clusters.len() {
            assert_eq!(newick::format_forest(&clusters[i]).unwrap(), expected_newicks[i]);
        }
    }
}
