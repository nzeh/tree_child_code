//! This module provides the basic methods for manipulating phylogenetic trees.
//!
//! It provides two types:
//!
//! A `Tree<T>` is a phylogenetic tree whose leaves have labels of type `T`.  The tree may be
//! binary or multifurcating.  
//!
//! A `TreeBuilder<T>` can be used to build a collection of trees, for example, when parsing a
//! Newick string.

use std::collections::HashMap;
use std::hash::Hash;
use std::slice;


/// A phylogenetic tree whose leaves have labels of some type `T`
#[derive(Clone)]
pub struct Tree<T> {

    /// The set of nodes in the tree
    nodes: Vec<Removable<NodeData<T>>>,

    /// The root of the tree
    root: Option<Node>,

    /// The set of leaves in the tree
    leaves: Vec<Option<Removable<Node>>>,

    /// Number of nodes in this tree
    node_count: usize,

    /// Number of leaves in this tree
    leaf_count: usize,
}


/// A marker type that holds on to an element and marks it as alive or dead
#[derive(Clone)]
struct Removable<T> {
    
    /// The stored item
    item: T,

    /// Is the item currently present?
    is_present: bool,
}


/// The data associated with a node
#[derive(Clone)]
struct NodeData<T> {

    /// Parent
    parent: Option<Node>,

    /// The leaf- or internal-node-specific data
    data: TypedNodeData<T>,
}


/// The part of the node data that's specific to leaves or internal nodes.
#[derive(Clone)]
enum TypedNodeData<T> {

    /// An leaf has an ID of type `Leaf` and a label of type `T`.
    Leaf(Leaf, T),

    /// An internal node has a list of children.
    Internal(Vec<Node>),
}


/// The type used to represent tree nodes
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Node(usize);


/// The type used to refer to leaves
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Leaf(usize);


/// An iterator over the nodes of a tree (see `Tree::nodes()`).
pub struct NodeIter<'a, T: 'a> {
    tree: &'a Tree<T>,
    node: usize,
    end:  usize,
}

/// An iterator over the leaves of a tree (see `Tree::leaves()`).
pub struct LeafIter<'a> {
    iter: slice::Iter<'a, Option<Removable<Node>>>,
}


/// An iterator over the children of a node (see `Tree::children()`).
pub struct ChildIter<'a> {
    iter: slice::Iter<'a, Node>,
}


impl<T> Removable<T> {

    /// Create a new removable item
    fn new(item: T) -> Removable<T> {
        Removable {
            item,
            is_present: true,
        }
    }

    /// Mark the item as removed
    fn remove(&mut self) {
        assert!(self.is_present, "double-removal of Removable");
        self.is_present = false;
    }

    /// Mark the item as present
    fn restore(&mut self) {
        assert!(!self.is_present, "double-restoration of Removable");
        self.is_present = true;
    }

    /// Provide a reference to the stored item
    fn item(&self) -> &T {
        assert!(self.is_present, "access to removed Removable");
        &self.item
    }

    /// Provide a reference to the stored item, without checking that the item is currently present
    fn item_unchecked(&self) -> &T {
        &self.item
    }

    /// Provide a mutable reference to a stored item
    fn item_mut(&mut self) -> &mut T {
        assert!(self.is_present, "access to removed Removable");
        &mut self.item
    }

    /// Is this removable present?
    fn is_present(&self) -> bool {
        self.is_present
    }
}


impl Node {

    /// Create a new node from an integer ID
    pub fn new(id: usize) -> Self {
        Node(id)
    }

    /// Extract the underlying integer ID
    pub fn id(self) -> usize {
        self.0
    }
}


impl Leaf {

    /// Create a new leaf from an integer ID
    pub fn new(id: usize) -> Self {
        Leaf(id)
    }

    /// Extract the underlying integer ID
    pub fn id(self) -> usize {
        self.0
    }
}


impl<T: Clone> Tree<T> {

    /// Create a new empty tree
    pub fn new() -> Self {
        Tree {
            nodes:      vec![],
            root:       None,
            leaves:     vec![],
            node_count: 0,
            leaf_count: 0,
        }
    }

    /// Return the number of nodes in the tree
    pub fn node_count(&self) -> usize {
        self.node_count
    }

    /// Return the number of leaves in the tree
    pub fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    /// Return the root of the tree.
    ///
    /// This is always `Some` node except when the tree has no nodes at all.
    pub fn root(&self) -> Option<Node> {
        self.root
    }

    /// Get an iterator over the nodes in the tree
    pub fn nodes(&self) -> NodeIter<T> {
        NodeIter {
            tree: self,
            node: 0,
            end:  self.nodes.len(),
        }
    }

    /// Get an iterator over the leaves in the tree
    pub fn leaves(&self) -> LeafIter {
        LeafIter {
            iter: self.leaves.iter(),
        }
    }

    /// Get an iterator over the children of a node
    pub fn children(&self, node: Node) -> ChildIter {
        ChildIter {
            iter: match self.node(node).data {
                TypedNodeData::Internal(ref children) => children.iter(),
                _                                     => [].iter(),
            },
        }
    }

    /// Get the parent of a node
    ///
    /// This is `Some` parent node if the node is not the root.  Otherwise, this is `None`.
    pub fn parent(&self, node: Node) -> Option<Node> {
        self.node(node).parent
    }

    /// Is this node a leaf?
    pub fn is_leaf(&self, node: Node) -> bool {
        match self.node(node).data {
            TypedNodeData::Leaf(_, _) => true,
            _                         => false,
        }
    }

    /// Get the leaf ID of this node
    ///
    /// This is `Some` leaf ID if the node is in fact a leaf.  Otherwise, this is `None`.
    pub fn leaf_id(&self, node: Node) -> Option<Leaf> {
        match self.node(node).data {
            TypedNodeData::Leaf(id, _) => Some(id),
            _                          => None,
        }
    }

    /// Get the label of this node, if it is a leaf
    ///
    /// This is `Some` leaf label if the node is in fact a leaf.  Otherwise, this is `None`.
    pub fn label(&self, node: Node) -> Option<&T> {
        match self.node(node).data {
            TypedNodeData::Leaf(_, ref label) => Some(label),
            _                                 => None,
        }
    }

    /// Get the list of leaf labels.  The output of `tree.labels()` is different from the output of
    /// `tree.leaves().map(|leaf| tree.label(leaf).unwrap())` because the latter returns only the
    /// labels of leaves that were not pruned from the tree.  In contrast, this method returns the
    /// labels of all leaves in the original input, pruned or not.
    pub fn labels(&self) -> Vec<T> {
        self.leaves.iter().filter_map(|leaf| {
            leaf.as_ref().map(|leaf| {
                let leaf = leaf.item_unchecked();
                let node = self.nodes[leaf.id()].item_unchecked();
                match node.data {
                    TypedNodeData::Leaf(_, ref label) => (*label).clone(),
                    _ => panic!("INTERNAL ERROR: Node associated with a leaf is not a leaf"),
                }
            })
        }).collect()
    }

    /// Get the node ID of the given leaf
    pub fn leaf(&self, leaf: Leaf) -> Node {
        *self.leaves[leaf.id()].as_ref().unwrap().item()
    }

    /// Prune the given leaf from the tree and return the parent, `None` if this leaf was the root.
    pub fn prune_leaf(&mut self, leaf: Leaf) -> Option<Node> {
        let node   = self.leaf(leaf);
        let parent = self.parent(node);

        if let Some(parent) = parent {
            self.remove_child(parent, node);
        } else {
            self.root = None;
        }

        self.leaves[leaf.id()].as_mut().unwrap().remove();
        self.nodes[node.id()].remove();
        self.leaf_count -= 1;
        self.node_count -= 1;

        parent
    }

    /// Reattach the given leaf to the tree.  It gets attached to the node that was the parent
    /// before it was removed.
    pub fn restore_leaf(&mut self, leaf: Leaf) {

        self.leaves[leaf.id()].as_mut().unwrap().restore();
        let node = self.leaf(leaf);
        self.nodes[node.id()].restore();
        self.leaf_count += 1;
        self.node_count += 1;

        if let Some(parent) = self.parent(node) {
            self.add_child(parent, node);
        } else {
            self.root = Some(node);
        }
    }

    /// Suppress a node with only one child and return the child
    pub fn suppress_node(&mut self, node: Node) -> Node {

        let child = self.internal_children(node)[0];

        let parent = self.parent(node);
        self.node_mut(child).parent = parent;
        if let Some(parent) = parent {
            self.replace_child(parent, node, child);
        } else {
            self.root = Some(child);
        }

        self.node_count -= 1;
        self.nodes[node.id()].remove();

        child
    }

    /// Restore a node that was suppressed before
    pub fn restore_node(&mut self, node: Node) {

        self.node_count += 1;
        self.nodes[node.id()].restore();

        let child = self.internal_children(node)[0];

        self.node_mut(child).parent = Some(node);
        if let Some(parent) = self.parent(node) {
            self.replace_child(parent, child, node);
        } else {
            self.root = Some(node);
        }
    }

    /// Add a child to a given node
    fn add_child(&mut self, parent: Node, child: Node) {
        let children = self.internal_children_mut(parent);
        children.push(child);
    }

    /// Remove a child from a given node
    fn remove_child(&mut self, parent: Node, child: Node) {
        let children = self.internal_children_mut(parent);
        match children.iter().position(|&c| c == child) {
            Some(pos) => { children.swap_remove(pos); },
            None      => panic!("Cannot remove nonexistent child!"),
        }
    }

    /// Rplace a child with a different child
    fn replace_child(&mut self, parent: Node, old_child: Node, new_child: Node) {
        let children = self.internal_children_mut(parent);
        for child in children.iter_mut() {
            if *child == old_child {
                *child = new_child;
                return;
            }
        }
        panic!("Cannot replace non-existent child!");
    }

    /// Access the node data for the given node
    fn node(&self, node: Node) -> &NodeData<T> {
        self.nodes[node.id()].item()
    }

    /// Access the node data mutably
    fn node_mut(&mut self, node: Node) -> &mut NodeData<T> {
        self.nodes[node.id()].item_mut()
    }

    /// Access the list of children of an internal node
    fn internal_children(&self, node: Node) -> &Vec<Node> {
        match self.node(node).data {
            TypedNodeData::Internal(ref children) => children,
            _ => panic!("Trying to access the children of a leaf!"),
        }
    }

    /// Mutably access the list of children of an internal node
    fn internal_children_mut(&mut self, node: Node) -> &mut Vec<Node> {
        match self.node_mut(node).data {
            TypedNodeData::Internal(ref mut children) => children,
            _ => panic!("Trying to access the children of a leaf!"),
        }
    }
}


impl<'a, T> Iterator for NodeIter<'a, T> {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        while self.node < self.end {
            if self.tree.nodes[self.node].is_present() {
                self.node += 1;
                return Some(Node::new(self.node - 1));
            }
            self.node += 1;
        }
        None
    }
}


impl<'a> Iterator for LeafIter<'a> {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        while let Some(leaf) = self.iter.next() {
            if let Some(leaf) = leaf {
                if leaf.is_present() {
                    return Some(*leaf.item());
                }
            }
        }
        None
    }
}


impl<'a> Iterator for ChildIter<'a> {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        self.iter.next().map(|node| *node)
    }
}


/// A structure to support the construction of a set of trees, both when parsing Newick strings and
/// when computing a cluster partition.  The construction guarantees that all leaves with the same
/// label in different trees receive the same leaf ID, so leaves in different trees can be matched
/// to each other during cluster partition or the search for a tree-child sequence based on their
/// IDs.
///
/// The `TreeBuilder` holds a "current tree" and a set of trees that were already built.
/// Initially, there is no current tree.
///
/// `TreeBuilder::new_tree()` creates a new empty tree and makes it the current tree.
///
/// `TreeBuilder::new_leaf()` adds a new leaf to the current tree.  This leaf is "floating" in the
/// sense that it does not have a parent yet.
///
/// `TreeBuilder::new_node()` takes a list of nodes in the current tree and creates a new node that
/// has these nodes as its children.
///
/// `TreeBuilder::finish_tree()` takes a "floating" node in the current tree as argument, makes this
/// node the root of the current tree, and then adds the current tree to the list of completely
/// built trees.  We're now back to not having a current tree.
///
/// The set of constructed trees is retrieved using `TreeBuilder::trees()`.
pub struct TreeBuilder<T> {

    /// The current tree under construction
    current_tree: Option<Tree<T>>,

    /// The set of trees already constructed
    trees: Vec<Tree<T>>,

    /// Hash map to map labels to leaf IDs to ensure leaves with the same label in different trees
    /// get the same ID.
    leaf_ids: HashMap<T, Leaf>,
}


impl<T> TreeBuilder<T>
where T: Clone + Eq + Hash {

    /// Create a new tree builder
    pub fn new() -> Self {
        TreeBuilder {
            current_tree: None,
            trees:        vec![],
            leaf_ids:     HashMap::new(),
        }
    }

    /// Create a new tree and make it the active tree
    pub fn new_tree(&mut self) {
        self.current_tree = Some(Tree::new());
    }

    /// Create a new leaf in the active tree
    pub fn new_leaf(&mut self, label: T) -> Node {

        let leaf_id = self.leaf_ids.len();
        let leaf    = self.leaf_ids.entry(label.clone()).or_insert(Leaf::new(leaf_id));

        self.current_tree.as_mut().map(|t| {
            let node = Node(t.nodes.len());
            while t.leaves.len() <= leaf.id() {
                t.leaves.push(None);
            }
            t.leaves[leaf.id()] = Some(Removable::new(node));
            t.nodes.push(Removable::new(NodeData {
                parent: None,
                data:   TypedNodeData::Leaf(*leaf, label),
            }));
            t.node_count += 1;
            t.leaf_count += 1;
            node
        }).unwrap()
    }

    /// Create a new node with the given list of children in the active tree
    pub fn new_node(&mut self, children: Vec<Node>) -> Node {
        self.current_tree.as_mut().map(|t| {
            let node = Node(t.nodes.len());
            for child in &children {
                t.node_mut(*child).parent = Some(node);
            }
            t.nodes.push(Removable::new(NodeData {
                parent: None,
                data:   TypedNodeData::Internal(children),
            }));
            t.node_count += 1;
            node
        }).unwrap()
    }

    /// Make the given node the root of the active tree and add the tree to the list of finished
    /// trees.  No tree is active afterwards.
    pub fn finish_tree(&mut self, root: Node) {
        self.current_tree.as_mut().map(|t| t.root = Some(root));
        self.trees.push(self.current_tree.take().unwrap());
    }

    /// Extract the list of built trees
    pub fn trees(self) -> Vec<Tree<T>> {
        self.trees
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    /// Test that leaf IDs convert correctly
    #[test]
    fn leaf_id() {
        let a = Leaf::new(3);
        let b = Leaf::new(8);
        assert_eq!(a.id(), 3);
        assert_eq!(b.id(), 8);
    }

    /// Test that node IDs convert correctly
    #[test]
    fn node_id() {
        let a = Node::new(13);
        let b = Node::new(0);
        assert_eq!(a.id(), 13);
        assert_eq!(b.id(), 0);
    }

    /// Test that an initial tree stores nothing
    #[test]
    fn tree_new() {
        let tree: Tree<u32> = Tree::new();
        assert_eq!(tree.root(), None);
        assert_eq!(tree.node_count(), 0);
        assert_eq!(tree.leaf_count(), 0);
        assert_eq!(tree.nodes().next(), None);
        assert_eq!(tree.leaves().next(), None);
    }

    /// Test that an initial tree builder generates no trees
    #[test]
    fn tree_builder_new() {
        let builder: TreeBuilder<u32> = TreeBuilder::new();
        assert!(builder.current_tree.is_none());
        assert_eq!(builder.trees().len(), 0);
    }

    /// Build a tree to be used in the remaining tests
    fn build_tree() -> Vec<Tree<u32>> {
        let mut builder: TreeBuilder<u32> = TreeBuilder::new();
        builder.new_tree();
        let a = builder.new_leaf(5);
        let b = builder.new_leaf(13);
        let c = builder.new_leaf(2);
        let d = builder.new_leaf(1);
        let e = builder.new_node(vec![a, c, d]);
        let f = builder.new_leaf(3);
        let g = builder.new_node(vec![f, b]);
        let h = builder.new_leaf(8);
        let r = builder.new_node(vec![e, g, h]);
        builder.finish_tree(r);
        builder.new_tree();
        let a = builder.new_leaf(13); // 1
        let b = builder.new_leaf(14); // 6
        let c = builder.new_leaf(2);  // 2
        let d = builder.new_leaf(8);  // 5
        let e = builder.new_leaf(9);  // 7
        let f = builder.new_node(vec![d, e, a]);
        let g = builder.new_node(vec![b, f]);
        let r = builder.new_node(vec![g, c]);
        builder.finish_tree(r);
        builder.trees()
    }

    /// Test the basic stats of the trees built using built_tree
    #[test]
    fn build_tree_basic_stats() {
        let trees = build_tree();
        assert_eq!(trees.len(), 2);
        assert_eq!(trees[0].node_count(), 9);
        assert_eq!(trees[1].node_count(), 8);
        assert_eq!(trees[0].leaf_count(), 6);
        assert_eq!(trees[1].leaf_count(), 5);
        assert_eq!(trees[0].root(), Some(Node::new(8)));
        assert_eq!(trees[1].root(), Some(Node::new(7)));
    }

    /// Test that the leaves are set up right
    #[test]
    fn build_tree_leaves() {
        let trees = build_tree();
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(1), Node::new(2), Node::new(3), Node::new(5), Node::new(7)]);
        assert_eq!(trees[0].leaf(Leaf::new(0)), Node::new(0));
        assert_eq!(trees[0].leaf(Leaf::new(1)), Node::new(1));
        assert_eq!(trees[0].leaf(Leaf::new(2)), Node::new(2));
        assert_eq!(trees[0].leaf(Leaf::new(3)), Node::new(3));
        assert_eq!(trees[0].leaf(Leaf::new(4)), Node::new(5));
        assert_eq!(trees[0].leaf(Leaf::new(5)), Node::new(7));
        assert_eq!(trees[0].label(trees[0].leaf(Leaf::new(0))), Some(&5));
        assert_eq!(trees[0].label(trees[0].leaf(Leaf::new(1))), Some(&13));
        assert_eq!(trees[0].label(trees[0].leaf(Leaf::new(2))), Some(&2));
        assert_eq!(trees[0].label(trees[0].leaf(Leaf::new(3))), Some(&1));
        assert_eq!(trees[0].label(trees[0].leaf(Leaf::new(4))), Some(&3));
        assert_eq!(trees[0].label(trees[0].leaf(Leaf::new(5))), Some(&8));
        assert_eq!(trees[0].leaf_id(trees[0].leaf(Leaf::new(0))), Some(Leaf::new(0)));
        assert_eq!(trees[0].leaf_id(trees[0].leaf(Leaf::new(1))), Some(Leaf::new(1)));
        assert_eq!(trees[0].leaf_id(trees[0].leaf(Leaf::new(2))), Some(Leaf::new(2)));
        assert_eq!(trees[0].leaf_id(trees[0].leaf(Leaf::new(3))), Some(Leaf::new(3)));
        assert_eq!(trees[0].leaf_id(trees[0].leaf(Leaf::new(4))), Some(Leaf::new(4)));
        assert_eq!(trees[0].leaf_id(trees[0].leaf(Leaf::new(5))), Some(Leaf::new(5)));
        assert_eq!(trees[1].leaves().collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(2), Node::new(3), Node::new(1), Node::new(4)]);
        assert_eq!(trees[1].leaf(Leaf::new(1)), Node::new(0));
        assert_eq!(trees[1].leaf(Leaf::new(2)), Node::new(2));
        assert_eq!(trees[1].leaf(Leaf::new(5)), Node::new(3));
        assert_eq!(trees[1].leaf(Leaf::new(6)), Node::new(1));
        assert_eq!(trees[1].leaf(Leaf::new(7)), Node::new(4));
        assert_eq!(trees[1].label(trees[1].leaf(Leaf::new(1))), Some(&13));
        assert_eq!(trees[1].label(trees[1].leaf(Leaf::new(2))), Some(&2));
        assert_eq!(trees[1].label(trees[1].leaf(Leaf::new(5))), Some(&8));
        assert_eq!(trees[1].label(trees[1].leaf(Leaf::new(6))), Some(&14));
        assert_eq!(trees[1].label(trees[1].leaf(Leaf::new(7))), Some(&9));
        assert_eq!(trees[1].leaf_id(trees[1].leaf(Leaf::new(1))), Some(Leaf::new(1)));
        assert_eq!(trees[1].leaf_id(trees[1].leaf(Leaf::new(2))), Some(Leaf::new(2)));
        assert_eq!(trees[1].leaf_id(trees[1].leaf(Leaf::new(5))), Some(Leaf::new(5)));
        assert_eq!(trees[1].leaf_id(trees[1].leaf(Leaf::new(6))), Some(Leaf::new(6)));
        assert_eq!(trees[1].leaf_id(trees[1].leaf(Leaf::new(7))), Some(Leaf::new(7)));
    }

    /// Test that the nodes iterator collects all nodes
    #[test]
    fn build_tree_nodes() {
        let trees = build_tree();
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(1), Node::new(2), Node::new(3), Node::new(4), 
        Node::new(5), Node::new(6), Node::new(7), Node::new(8)]);
        assert_eq!(trees[1].nodes().collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(1), Node::new(2), Node::new(3), Node::new(4), 
        Node::new(5), Node::new(6), Node::new(7)]);
    }

    /// Test that is_leaf reports the right nodes as leaves
    #[test]
    fn build_tree_is_leaf() {
        let trees        = build_tree();
        let mut nodes0   = trees[0].nodes();
        let mut answers0 = vec![true, true, true, true, false, true, false, true, false]
            .into_iter();
        let mut nodes1   = trees[1].nodes();
        let mut answers1 = vec![true, true, true, true, true, false, false, false]
            .into_iter();
        for _ in 0..9 {
            assert_eq!(trees[0].is_leaf(nodes0.next().unwrap()), answers0.next().unwrap());
        }
        for _ in 0..8 {
            assert_eq!(trees[1].is_leaf(nodes1.next().unwrap()), answers1.next().unwrap());
        }
    }

    /// Test that the children of each internal node are reported correctly
    #[test]
    fn build_tree_children() {
        let trees = build_tree();
        assert_eq!(trees[0].children(Node::new(4)).collect::<Vec<Node>>(),
        vec![Node::new(0), Node::new(2), Node::new(3)]);
        assert_eq!(trees[0].children(Node::new(6)).collect::<Vec<Node>>(),
        vec![Node::new(5), Node::new(1)]);
        assert_eq!(trees[0].children(Node::new(8)).collect::<Vec<Node>>(),
        vec![Node::new(4), Node::new(6), Node::new(7)]);
        assert_eq!(trees[1].children(Node::new(5)).collect::<Vec<Node>>(),
        vec![Node::new(3), Node::new(4), Node::new(0)]);
        assert_eq!(trees[1].children(Node::new(6)).collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(5)]);
        assert_eq!(trees[1].children(Node::new(7)).collect::<Vec<Node>>(),
        vec![Node::new(6), Node::new(2)]);
    }

    /// Test that parents are reported correctly
    #[test]
    fn build_tree_parents() {
        let trees        = build_tree();
        let mut nodes0   = trees[0].nodes();
        let mut answers0 = [
            Some(4), Some(6), Some(4), Some(4), Some(8), Some(6), Some(8), Some(8), None]
                .into_iter();
        let mut nodes1   = trees[1].nodes();
        let mut answers1 = [
            Some(5), Some(6), Some(7), Some(5), Some(5), Some(6), Some(7), None]
                .into_iter();
        for _ in 0..9 {
            assert_eq!(trees[0].parent(nodes0.next().unwrap()),
            answers0.next().unwrap().map(|id| Node::new(id)));
        }
        for _ in 0..8 {
            assert_eq!(trees[1].parent(nodes1.next().unwrap()),
            answers1.next().unwrap().map(|id| Node::new(id)));
        }
    }

    /// Test that remove_leaf and restore_leaf interact with each other nicely
    #[test]
    fn tree_remove_restore_leaf() {
        let mut trees = build_tree();
        let leaf1   = Leaf::new(3);
        let leaf2   = Leaf::new(1);
        let parent1 = Node::new(4);
        let parent2 = Node::new(6);

        trees[0].prune_leaf(leaf1);
        assert_eq!(trees[0].leaf_count(), 5);
        assert_eq!(trees[0].node_count(), 8);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(5), Node(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(4), Node(5), Node(6), Node(7), Node(8)]);
        assert_eq!(trees[0].children(parent1).collect::<Vec<Node>>(), vec![Node(0), Node(2)]);

        trees[0].prune_leaf(leaf2);
        assert_eq!(trees[0].leaf_count(), 4);
        assert_eq!(trees[0].node_count(), 7);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(), vec![
                   Node(0), Node(2), Node(5), Node(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(), vec![
                   Node(0), Node(2), Node(4), Node(5), Node(6), Node(7), Node(8)]);
        assert_eq!(trees[0].children(parent1).collect::<Vec<Node>>(), vec![Node(0), Node(2)]);
        assert_eq!(trees[0].children(parent2).collect::<Vec<Node>>(), vec![Node(5)]);

        trees[0].restore_leaf(leaf2);
        assert_eq!(trees[0].leaf_count(), 5);
        assert_eq!(trees[0].node_count(), 8);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(5), Node(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(4), Node(5), Node(6), Node(7), Node(8)]);
        assert_eq!(trees[0].children(parent1).collect::<Vec<Node>>(), vec![Node(0), Node(2)]);
        assert_eq!(trees[0].children(parent2).collect::<Vec<Node>>(), vec![Node(5), Node(1)]);

        trees[0].restore_leaf(leaf1);
        assert_eq!(trees[0].leaf_count(), 6);
        assert_eq!(trees[0].node_count(), 9);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(3), Node(5), Node(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(3), Node(4),
                   Node(5), Node(6), Node(7), Node(8)]);
        assert_eq!(trees[0].children(parent1).collect::<Vec<Node>>(), vec![
                   Node(0), Node(2), Node(3)]);
        assert_eq!(trees[0].children(parent2).collect::<Vec<Node>>(), vec![Node(5), Node(1)]);

        trees[0].prune_leaf(leaf1);
        assert_eq!(trees[0].leaf_count(), 5);
        assert_eq!(trees[0].node_count(), 8);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(5), Node(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(), vec![
                   Node(0), Node(1), Node(2), Node(4), Node(5), Node(6), Node(7), Node(8)]);
        assert_eq!(trees[0].children(parent1).collect::<Vec<Node>>(), vec![Node(0), Node(2)]);

        trees[0].prune_leaf(leaf2);
        assert_eq!(trees[0].leaf_count(), 4);
        assert_eq!(trees[0].node_count(), 7);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(), vec![
                   Node(0), Node(2), Node(5), Node(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(), vec![
                   Node(0), Node(2), Node(4), Node(5), Node(6), Node(7), Node(8)]);
        assert_eq!(trees[0].children(parent1).collect::<Vec<Node>>(), vec![Node(0), Node(2)]);
        assert_eq!(trees[0].children(parent2).collect::<Vec<Node>>(), vec![Node(5)]);
    }

    /// Check that suppressing and restoring nodes does the right thing
    #[test]
    fn tree_suppress_restore_node() {
        let mut trees = build_tree();
        let leaf1   = Leaf::new(0);
        let leaf2   = Leaf::new(3);
        let leaf3   = Leaf::new(4);
        let node1   = Node::new(4);
        let node2   = Node::new(6);
        let parent  = Node::new(8);
        trees[0].prune_leaf(leaf1);
        trees[0].prune_leaf(leaf2);
        trees[0].prune_leaf(leaf3);
        assert_eq!(trees[0].leaf_count(), 3);
        assert_eq!(trees[0].node_count(), 6);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(4), Node::new(6), Node::new(7), Node::new(8)]);

        trees[0].suppress_node(node1);
        assert_eq!(trees[0].leaf_count(), 3);
        assert_eq!(trees[0].node_count(), 5);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(6), Node::new(7), Node::new(8)]);
        assert_eq!(trees[0].children(parent).collect::<Vec<Node>>(),
        vec![Node::new(2), Node::new(6), Node::new(7)]);

        trees[0].suppress_node(node2);
        assert_eq!(trees[0].leaf_count(), 3);
        assert_eq!(trees[0].node_count(), 4);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(7), Node::new(8)]);
        assert_eq!(trees[0].children(parent).collect::<Vec<Node>>(),
        vec![Node::new(2), Node::new(1), Node::new(7)]);

        trees[0].restore_node(node2);
        assert_eq!(trees[0].leaf_count(), 3);
        assert_eq!(trees[0].node_count(), 5);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(6), Node::new(7), Node::new(8)]);
        assert_eq!(trees[0].children(parent).collect::<Vec<Node>>(),
        vec![Node::new(2), Node::new(6), Node::new(7)]);

        trees[0].restore_node(node1);
        assert_eq!(trees[0].leaf_count(), 3);
        assert_eq!(trees[0].node_count(), 6);
        assert_eq!(trees[0].leaves().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(7)]);
        assert_eq!(trees[0].nodes().collect::<Vec<Node>>(),
        vec![Node::new(1), Node::new(2), Node::new(4), Node::new(6), Node::new(7), Node::new(8)]);
        assert_eq!(trees[0].children(parent).collect::<Vec<Node>>(),
        vec![Node::new(4), Node::new(6), Node::new(7)]);
    }
}
