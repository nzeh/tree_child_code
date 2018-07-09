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
    tree: Tree<T>,

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
    pub fn tree(&self) -> &Tree<T> {
        &self.tree
    }

    /// Access to the reticulation labels of the nodes
    pub fn reticulations(&self) -> &HashMap<Node, usize> {
        &self.reticulations
    }
}

/// The state of building the network
struct NetBuilder<T> {

    /// A tree builder for building the tree structure of the network
    builder: TreeBuilder<T>,

    /// The HashMap of reticulation labels
    reticulations: HashMap<Node, usize>,

    /// The next available reticulation ID
    next_reticulation: usize,

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
        NetBuilder { builder, reticulations, next_reticulation: 0, nodes }
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
        let vnode = self.get_node(&v);
        let unode = self.builder.new_leaf(Default::default());
        let node  = self.builder.new_node(vec![unode, vnode]);
        self.reticulations.insert(unode, uret);
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
            *self.nodes.get(u).unwrap()
        } else {
            let node = self.builder.new_leaf(u.clone());
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
            *self.nodes.get_mut(&u).unwrap() = node;
            ret
        }
    }
}
