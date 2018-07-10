//! This module implements a structure for representing tree-child networks in a form ready to be
//! translated to extended Newick format.

use std::collections::HashMap;
use std::hash::Hash;
use tree::{Node, Tree, TreeBuilder};
use tree_child_sequence::{Pair, TcSeq};

/// A structure to represent a tree-child network.  The Newick output represents this as a tree
/// with nodes annotated with their "association" labels.  Thus, we choose the same representation
/// internally.
pub struct TcNet<T> {

    /// The underlying tree structure of the network
    tree: Tree<TcNetLeaf<T>>,

    /// The "association labels" corresponding to reticulations
    reticulations: HashMap<Node, usize>,

}

impl<T: Clone + Default + Eq + Hash> TcNet<T> {

    /// Create a tree-child network from a given tree-child sequence
    pub fn from_seq(seq: TcSeq<T>) -> Self {
        let mut builder = NetBuilder::new();
        for pair in seq {
            match pair {
                Pair::Trivial(u, v)    => builder.add_cherry(u, v),
                Pair::NonTrivial(u, v) => builder.add_reticulated_cherry(u, v),
                Pair::Final(u)         => builder.set_root(u),
            }
        }
        builder.network()
    }

    /// Access to the tree structure of the nework
    pub fn tree(&self) -> &Tree<TcNetLeaf<T>> {
        &self.tree
    }

    /// Access to the reticulation labels of the nodes
    pub fn reticulations(&self) -> &HashMap<Node, usize> {
        &self.reticulations
    }
}

/// The label type of the tree representing a tree-child network
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TcNetLeaf<T> {

    /// A reticulation leaf
    Reticulation(usize),

    /// An original leaf
    Leaf(T),
}

/// The state of building the network
struct NetBuilder<T> {

    /// A tree builder for building the tree structure of the network
    builder: TreeBuilder<TcNetLeaf<T>>,

    /// The HashMap of reticulation labels
    reticulations: HashMap<Node, usize>,

    /// The next available reticulation ID
    next_reticulation: usize,

    /// The next available reticulation leaf ID
    next_reticulation_leaf: usize,

    /// A HashMap of nodes currently representing leaf labels
    nodes: HashMap<T, Node>,
}

impl<T: Clone + Default + Eq + Hash> NetBuilder<T> {

    /// Create a new `NetBuilder`
    fn new() -> Self {
        let mut builder   = TreeBuilder::new();
        let reticulations = HashMap::new();
        let nodes         = HashMap::new();
        builder.new_tree();
        NetBuilder {
            builder,
            reticulations,
            next_reticulation:      0,
            next_reticulation_leaf: 0,
            nodes
        }
    }

    /// Record a non-reticulated cherry in the network
    fn add_cherry(&mut self, u: T, v: T) {
        let unode = self.get_node(&u);
        let vnode = self.get_node(&v);
        let node  = self.builder.new_node(vec![unode, vnode]);
        *self.nodes.get_mut(&v).unwrap() = node;
    }

    /// Record a reticulated cherry in the network
    fn add_reticulated_cherry(&mut self, u: T, v: T) {
        let uret  = self.get_reticulation(&u);
        let ulbl  = self.next_reticulation_leaf;
        self.next_reticulation_leaf += 1;
        let vnode = self.get_node(&v);
        let unode = self.builder.new_leaf(TcNetLeaf::Reticulation(ulbl));
        self.reticulations.insert(unode, uret);
        let node  = self.builder.new_node(vec![unode, vnode]);
        *self.nodes.get_mut(&v).unwrap() = node;
    }

    /// Set the root of the network
    fn set_root(&mut self, u: T) {
        let node = self.get_node(&u);
        self.builder.finish_tree(node);
    }

    /// Retrieve the final network
    fn network(self) -> TcNet<T> {
        let mut trees = self.builder.trees();
        TcNet {
            tree: trees.pop().unwrap(),
            reticulations: self.reticulations,
        }
    }

    /// Get the node corresponding to a label
    fn get_node(&mut self, u: &T) -> Node {
        if self.nodes.contains_key(u) {
            let node = *self.nodes.get(u).unwrap();
            node
        } else {
            let node = self.builder.new_leaf(TcNetLeaf::Leaf(u.clone()));
            self.nodes.insert(u.clone(), node);
            node
        }
    }

    /// Get the reticulation corresponding to a label
    fn get_reticulation(&mut self, u: &T) -> usize {
        let node = self.get_node(u);
        if self.reticulations.contains_key(&node) {
            *self.reticulations.get(&node).unwrap()
        } else {
            let node = self.builder.new_node(vec![node]);
            let ret  = self.next_reticulation;
            self.next_reticulation += 1;
            self.reticulations.insert(node, ret);
            *self.nodes.get_mut(u).unwrap() = node;
            ret
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    // I cannot easily test the operation of the individual functions because they manipulate the
    // tree builder state, which is not observable from here.  For now, I'll simply test with three
    // inputs that the output produced from a tree child sequences matches my expectations.

    /// Test that a tree-child sequence with only trivial pairs results in a network that is a
    /// tree.
    #[test]
    fn trivial_tc_seq() {
        let seq = vec![
            Pair::Trivial(1, 2),
            Pair::Trivial(3, 4),
            Pair::Trivial(2, 4),
            Pair::Trivial(5, 6),
            Pair::Trivial(4, 6),
            Pair::Final(6),
        ];
        let network = TcNet::from_seq(seq);
        let tree = network.tree();
        assert_eq!(tree.leaves().collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(1), Node::new(3), Node::new(4), Node::new(7), Node::new(8)]);
        assert_eq!(tree.label(Node::new(0)), Some(&TcNetLeaf::Leaf(1)));
        assert_eq!(tree.label(Node::new(1)), Some(&TcNetLeaf::Leaf(2)));
        assert_eq!(tree.label(Node::new(2)), None);
        assert_eq!(tree.label(Node::new(3)), Some(&TcNetLeaf::Leaf(3)));
        assert_eq!(tree.label(Node::new(4)), Some(&TcNetLeaf::Leaf(4)));
        assert_eq!(tree.label(Node::new(5)), None);
        assert_eq!(tree.label(Node::new(6)), None);
        assert_eq!(tree.label(Node::new(7)), Some(&TcNetLeaf::Leaf(5)));
        assert_eq!(tree.label(Node::new(8)), Some(&TcNetLeaf::Leaf(6)));
        assert_eq!(tree.label(Node::new(9)), None);
        assert_eq!(tree.label(Node::new(10)), None);
        assert_eq!(tree.parent(Node::new(0)), Some(Node::new(2)));
        assert_eq!(tree.parent(Node::new(1)), Some(Node::new(2)));
        assert_eq!(tree.parent(Node::new(2)), Some(Node::new(6)));
        assert_eq!(tree.parent(Node::new(3)), Some(Node::new(5)));
        assert_eq!(tree.parent(Node::new(4)), Some(Node::new(5)));
        assert_eq!(tree.parent(Node::new(5)), Some(Node::new(6)));
        assert_eq!(tree.parent(Node::new(6)), Some(Node::new(10)));
        assert_eq!(tree.parent(Node::new(7)), Some(Node::new(9)));
        assert_eq!(tree.parent(Node::new(8)), Some(Node::new(9)));
        assert_eq!(tree.parent(Node::new(9)), Some(Node::new(10)));
        assert_eq!(tree.parent(Node::new(10)), None);
        for i in 0..10 {
            assert_eq!(network.reticulations().get(&Node::new(i)), None);
        }
    }

    /// Test that the network constructed from a simple input with one reticulation has the correct
    /// shape.
    #[test]
    fn simple_one_reticulation() {
        let seq = vec![
            Pair::NonTrivial(2, 1),
            Pair::Trivial(2, 3),
            Pair::Trivial(3, 1),
            Pair::Final(1),
        ];
        let network = TcNet::from_seq(seq);
        let tree = network.tree();
        assert_eq!(tree.leaves().collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(2), Node::new(3), Node::new(5)]);
        assert_eq!(tree.label(Node::new(0)), Some(&TcNetLeaf::Leaf(2)));
        assert_eq!(tree.label(Node::new(1)), None);
        assert_eq!(tree.label(Node::new(2)), Some(&TcNetLeaf::Leaf(1)));
        assert_eq!(tree.label(Node::new(3)), Some(&TcNetLeaf::Reticulation(0)));
        assert_eq!(tree.label(Node::new(4)), None);
        assert_eq!(tree.label(Node::new(5)), Some(&TcNetLeaf::Leaf(3)));
        assert_eq!(tree.label(Node::new(6)), None);
        assert_eq!(tree.label(Node::new(7)), None);
        assert_eq!(tree.parent(Node::new(0)), Some(Node::new(1)));
        assert_eq!(tree.parent(Node::new(1)), Some(Node::new(6)));
        assert_eq!(tree.parent(Node::new(2)), Some(Node::new(4)));
        assert_eq!(tree.parent(Node::new(3)), Some(Node::new(4)));
        assert_eq!(tree.parent(Node::new(4)), Some(Node::new(7)));
        assert_eq!(tree.parent(Node::new(5)), Some(Node::new(6)));
        assert_eq!(tree.parent(Node::new(6)), Some(Node::new(7)));
        assert_eq!(tree.parent(Node::new(7)), None);
        assert_eq!(network.reticulations().get(&Node::new(0)), None);
        assert_eq!(network.reticulations().get(&Node::new(1)), Some(&0));
        assert_eq!(network.reticulations().get(&Node::new(2)), None);
        assert_eq!(network.reticulations().get(&Node::new(3)), Some(&0));
        assert_eq!(network.reticulations().get(&Node::new(4)), None);
        assert_eq!(network.reticulations().get(&Node::new(5)), None);
        assert_eq!(network.reticulations().get(&Node::new(6)), None);
        assert_eq!(network.reticulations().get(&Node::new(7)), None);
    }

    /// Test that the network constructed from a more complex input with three reticulations has
    /// the correct shape.
    #[test]
    fn complex_three_reticulations() {
        let seq = vec![
            Pair::Trivial(7, 5),
            Pair::NonTrivial(1, 3),
            Pair::NonTrivial(3, 5),
            Pair::Trivial(3, 4),
            Pair::NonTrivial(6, 8),
            Pair::NonTrivial(1, 4),
            Pair::NonTrivial(6, 5),
            Pair::Trivial(6, 2),
            Pair::Trivial(5, 8),
            Pair::Trivial(2, 8),
            Pair::Trivial(1, 8),
            Pair::Trivial(4, 8),
            Pair::Final(8),
        ];
        let network = TcNet::from_seq(seq);
        let tree = network.tree();
        assert_eq!(tree.leaf_count(), 13);
        assert_eq!(tree.leaves().collect::<Vec<Node>>(),
        vec![
        Node::new(0), Node::new(1), Node::new(3), Node::new(5), Node::new(6),
        Node::new(9), Node::new(11), Node::new(13), Node::new(15), Node::new(16),
        Node::new(18), Node::new(20), Node::new(22),
        ]);
        assert_eq!(tree.label(Node::new(0)), Some(&TcNetLeaf::Leaf(7)));
        assert_eq!(tree.label(Node::new(1)), Some(&TcNetLeaf::Leaf(5)));
        assert_eq!(tree.label(Node::new(2)), None);
        assert_eq!(tree.label(Node::new(3)), Some(&TcNetLeaf::Leaf(1)));
        assert_eq!(tree.label(Node::new(4)), None);
        assert_eq!(tree.label(Node::new(5)), Some(&TcNetLeaf::Leaf(3)));
        assert_eq!(tree.label(Node::new(6)), Some(&TcNetLeaf::Reticulation(0)));
        assert_eq!(tree.label(Node::new(7)), None);
        assert_eq!(tree.label(Node::new(8)), None);
        assert_eq!(tree.label(Node::new(9)), Some(&TcNetLeaf::Reticulation(1)));
        assert_eq!(tree.label(Node::new(10)), None);
        assert_eq!(tree.label(Node::new(11)), Some(&TcNetLeaf::Leaf(4)));
        assert_eq!(tree.label(Node::new(12)), None);
        assert_eq!(tree.label(Node::new(13)), Some(&TcNetLeaf::Leaf(6)));
        assert_eq!(tree.label(Node::new(14)), None);
        assert_eq!(tree.label(Node::new(15)), Some(&TcNetLeaf::Leaf(8)));
        assert_eq!(tree.label(Node::new(16)), Some(&TcNetLeaf::Reticulation(2)));
        assert_eq!(tree.label(Node::new(17)), None);
        assert_eq!(tree.label(Node::new(18)), Some(&TcNetLeaf::Reticulation(3)));
        assert_eq!(tree.label(Node::new(19)), None);
        assert_eq!(tree.label(Node::new(20)), Some(&TcNetLeaf::Reticulation(4)));
        assert_eq!(tree.label(Node::new(21)), None);
        assert_eq!(tree.label(Node::new(22)), Some(&TcNetLeaf::Leaf(2)));
        assert_eq!(tree.label(Node::new(23)), None);
        assert_eq!(tree.label(Node::new(24)), None);
        assert_eq!(tree.label(Node::new(25)), None);
        assert_eq!(tree.label(Node::new(26)), None);
        assert_eq!(tree.label(Node::new(27)), None);
        assert_eq!(tree.parent(Node::new(0)), Some(Node::new(2)));
        assert_eq!(tree.parent(Node::new(1)), Some(Node::new(2)));
        assert_eq!(tree.parent(Node::new(2)), Some(Node::new(10)));
        assert_eq!(tree.parent(Node::new(3)), Some(Node::new(4)));
        assert_eq!(tree.parent(Node::new(4)), Some(Node::new(26)));
        assert_eq!(tree.parent(Node::new(5)), Some(Node::new(7)));
        assert_eq!(tree.parent(Node::new(6)), Some(Node::new(7)));
        assert_eq!(tree.parent(Node::new(7)), Some(Node::new(8)));
        assert_eq!(tree.parent(Node::new(8)), Some(Node::new(12)));
        assert_eq!(tree.parent(Node::new(9)), Some(Node::new(10)));
        assert_eq!(tree.parent(Node::new(10)), Some(Node::new(21)));
        assert_eq!(tree.parent(Node::new(11)), Some(Node::new(12)));
        assert_eq!(tree.parent(Node::new(12)), Some(Node::new(19)));
        assert_eq!(tree.parent(Node::new(13)), Some(Node::new(14)));
        assert_eq!(tree.parent(Node::new(14)), Some(Node::new(23)));
        assert_eq!(tree.parent(Node::new(15)), Some(Node::new(17)));
        assert_eq!(tree.parent(Node::new(16)), Some(Node::new(17)));
        assert_eq!(tree.parent(Node::new(17)), Some(Node::new(24)));
        assert_eq!(tree.parent(Node::new(18)), Some(Node::new(19)));
        assert_eq!(tree.parent(Node::new(19)), Some(Node::new(27)));
        assert_eq!(tree.parent(Node::new(20)), Some(Node::new(21)));
        assert_eq!(tree.parent(Node::new(21)), Some(Node::new(24)));
        assert_eq!(tree.parent(Node::new(22)), Some(Node::new(23)));
        assert_eq!(tree.parent(Node::new(23)), Some(Node::new(25)));
        assert_eq!(tree.parent(Node::new(24)), Some(Node::new(25)));
        assert_eq!(tree.parent(Node::new(25)), Some(Node::new(26)));
        assert_eq!(tree.parent(Node::new(26)), Some(Node::new(27)));
        assert_eq!(tree.parent(Node::new(27)), None);
        assert_eq!(network.reticulations().get(&Node::new(0)), None);
        assert_eq!(network.reticulations().get(&Node::new(1)), None);
        assert_eq!(network.reticulations().get(&Node::new(2)), None);
        assert_eq!(network.reticulations().get(&Node::new(3)), None);
        assert_eq!(network.reticulations().get(&Node::new(4)), Some(&0));
        assert_eq!(network.reticulations().get(&Node::new(5)), None);
        assert_eq!(network.reticulations().get(&Node::new(6)), Some(&0));
        assert_eq!(network.reticulations().get(&Node::new(7)), None);
        assert_eq!(network.reticulations().get(&Node::new(8)), Some(&1));
        assert_eq!(network.reticulations().get(&Node::new(9)), Some(&1));
        assert_eq!(network.reticulations().get(&Node::new(10)), None);
        assert_eq!(network.reticulations().get(&Node::new(11)), None);
        assert_eq!(network.reticulations().get(&Node::new(12)), None);
        assert_eq!(network.reticulations().get(&Node::new(13)), None);
        assert_eq!(network.reticulations().get(&Node::new(14)), Some(&2));
        assert_eq!(network.reticulations().get(&Node::new(15)), None);
        assert_eq!(network.reticulations().get(&Node::new(16)), Some(&2));
        assert_eq!(network.reticulations().get(&Node::new(17)), None);
        assert_eq!(network.reticulations().get(&Node::new(18)), Some(&0));
        assert_eq!(network.reticulations().get(&Node::new(19)), None);
        assert_eq!(network.reticulations().get(&Node::new(20)), Some(&2));
        assert_eq!(network.reticulations().get(&Node::new(21)), None);
        assert_eq!(network.reticulations().get(&Node::new(22)), None);
        assert_eq!(network.reticulations().get(&Node::new(23)), None);
        assert_eq!(network.reticulations().get(&Node::new(24)), None);
        assert_eq!(network.reticulations().get(&Node::new(25)), None);
        assert_eq!(network.reticulations().get(&Node::new(26)), None);
        assert_eq!(network.reticulations().get(&Node::new(27)), None);
    }
}
