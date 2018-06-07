use std::collections::HashMap;
use std::hash::Hash;
use std::slice;


/// The traits for interacting with trees
pub mod traits {

    /// The trait that needs to be implemented by identifier types
    pub trait Id {

        /// Create an ID corresponding to the given integer
        fn new(id: usize) -> Self;

        /// Access the integer wrapped by the ID
        fn id(self) -> usize;
    }

    /// A tree accessor trait used by the Newick writer and other parts of the code to explore a
    /// tree.
    pub trait Tree<'a, T: 'a> {

        /// The node type for the tree
        type Node: Clone + Copy + Id + PartialEq + Ord;

        /// The type used to identify leaves
        type Leaf: Clone + Copy + Id + PartialEq + Ord;

        /// An iterator over the nodes of the tree
        type NodeIter: Iterator<Item=Self::Node>;

        /// An iterator over the leaves of the tree
        type LeafIter: Iterator<Item=Self::Node>;

        /// An iterator over the children of a node
        type ChildIter: Iterator<Item=Self::Node>;

        /// Create a new tree
        fn new() -> Self;

        /// Access the number of nodes in the tree
        fn node_count(&self) -> usize;

        /// Access the number of leaves in the tree
        fn leaf_count(&self) -> usize;

        /// Access the root of the next tree
        fn root(&self) -> Option<Self::Node>;

        /// Access the nodes of the tree
        fn nodes(&self) -> Self::NodeIter;

        /// Access the leaves of the tree
        fn leaves(&'a self) -> Self::LeafIter;

        /// Access the children of a node
        fn children(&'a self, node: Self::Node) -> Self::ChildIter;

        /// Access the parent of a node
        fn parent(&'a self, node: Self::Node) -> Option<Self::Node>;

        /// Access the left sibling of a node
        fn left(&'a self, node: Self::Node) -> Option<Self::Node>;

        /// Access the right sibling of a node
        fn right(&'a self, node: Self::Node) -> Option<Self::Node>;

        /// Is this node a leaf?
        fn is_leaf(&'a self, node: Self::Node) -> bool;

        /// Access the leaf's ID
        fn leaf_id(&'a self, node: Self::Node) -> Option<Self::Leaf>;

        /// Access the leaf's label
        fn label(&'a self, node: Self::Node) -> Option<&T>;

        /// Access the node identified by a given leaf ID
        fn leaf(&'a self, leaf: Self::Leaf) -> Self::Node;

        /// Prune a leaf from the tree without removing it from the list of leaves
        fn prune_leaf(&'a mut self, leaf: Self::Leaf);

        /// Restore a pruned leaf by reattaching it to its parent
        fn restore_leaf(&'a mut self, leaf: Self::Leaf);
    }

    /// A tree builder trait used by the Newick parser and other parts of the code to construct a
    /// tree or forest.
    pub trait TreeBuilder<T> {

        /// The node type for the tree
        type Node: Clone + Copy;

        /// The tree type being constructed
        type Tree;

        /// Create a new tree builder
        fn new() -> Self;

        /// Allocate a new tree
        fn new_tree(&mut self);

        /// Create a new leaf in the current tree
        fn new_leaf(&mut self, label: T) -> Self::Node;

        /// Create a new internal node with the given set of children in the current tree.
        fn new_node(&mut self, children: Vec<Self::Node>) -> Self::Node;

        /// Finish the construction of this tree and make the given node its root.
        fn finish_tree(&mut self, root: Self::Node);

        /// Retrieve the constructed trees
        fn trees(self) -> Vec<Self::Tree>;
    }
}


use tree::traits::Id;
use tree::traits::Tree as TreeTrait;


/// A phylogenetic tree whose leaves have `usize` labels
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
struct Removable<T> {
    
    /// The stored item
    item: T,

    /// Is the item currently present?
    is_present: bool,
}


/// The data associated with a node
struct NodeData<T> {

    /// Parent
    parent: Option<Node>,

    /// Left sibling
    left: Option<Node>,

    /// Right sibling
    right: Option<Node>,

    /// The leaf- or internal-node-specific data
    data: TypedNodeData<T>,
}


/// The part of the node data that's specific to leaves or internal nodes.
enum TypedNodeData<T> {

    /// An leaf has an ID of type `Leaf` and a label of type `T`.
    Leaf(Leaf, T),

    /// An internal node has a child.
    Internal(Node),
}


/// The type used to represent tree nodes
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Node(usize);


/// The type used to refer to leaves
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Leaf(usize);


/// An iterator over the nodes of a tree
pub struct NodeIter<'a, T: 'a> {
    tree: &'a Tree<T>,
    node: usize,
    end:  usize,
}

/// An iterator over the leaves of a tree
pub struct LeafIter<'a> {
    iter: slice::Iter<'a, Option<Removable<Node>>>,
}


/// An iterator over the children of a node
pub struct ChildIter<'a, T: 'a> {
    tree:  &'a Tree<T>,
    child: Option<Node>,
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


impl traits::Id for Node {

    fn new(id: usize) -> Self {
        Node(id)
    }

    fn id(self) -> usize {
        self.0
    }
}


impl traits::Id for Leaf {

    fn new(id: usize) -> Self {
        Leaf(id)
    }

    fn id(self) -> usize {
        self.0
    }
}


impl<'a, T: 'a> traits::Tree<'a, T> for Tree<T> {

    type Node = Node;

    type Leaf = Leaf;

    type NodeIter = NodeIter<'a, T>;

    type LeafIter = LeafIter<'a>;

    type ChildIter = ChildIter<'a, T>;

    fn new() -> Self {
        Tree {
            nodes:      vec![],
            root:       None,
            leaves:     vec![],
            node_count: 0,
            leaf_count: 0,
        }
    }

    fn node_count(&self) -> usize {
        self.node_count
    }

    fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    fn root(&self) -> Option<Node> {
        self.root
    }

    // TODO: Iterate only over the nodes that are alive
    fn nodes(&self) -> NodeIter<'a, T> {
        NodeIter {
            tree: self,
            node: 0,
            end:  self.nodes.len(),
        }
    }

    // TODO: Iterate only over the leaves that are alive
    fn leaves(&'a self) -> LeafIter<'a> {
        LeafIter {
            iter: self.leaves.iter(),
        }
    }

    fn children(&'a self, node: Node) -> ChildIter<'a, T> {
        ChildIter {
            tree:  self,
            child: match self.node(node).data {
                TypedNodeData::Internal(child) => Some(child),
                _                              => None,
            },
        }
    }

    fn parent(&self, node: Node) -> Option<Node> {
        self.node(node).parent
    }

    fn left(&self, node: Node) -> Option<Node> {
        self.node(node).left
    }

    fn right(&self, node: Node) -> Option<Node> {
        self.node(node).right
    }

    fn is_leaf(&self, node: Node) -> bool {
        match self.node(node).data {
            TypedNodeData::Leaf(_, _) => true,
            _                         => false,
        }
    }

    fn leaf_id(&self, node: Node) -> Option<Leaf> {
        match self.node(node).data {
            TypedNodeData::Leaf(id, _) => Some(id),
            _                          => None,
        }
    }

    fn label(&self, node: Node) -> Option<&T> {
        match self.node(node).data {
            TypedNodeData::Leaf(_, ref label) => Some(label),
            _                                 => None,
        }
    }

    fn leaf(&self, leaf: Leaf) -> Node {
        *self.leaves[leaf.id()].as_ref().unwrap().item()
    }

    fn prune_leaf(&mut self, leaf: Leaf) {
        let node = self.leaf(leaf);
        self.leaves[leaf.id()].as_mut().unwrap().remove();
        self.leaf_count -= 1;
        match self.parent(node) {
            Some(parent) => {
                let left  = self.left(node);
                let right = self.right(node);
                match left {
                    Some(left) => {
                        self.nodes[left.id()].item_mut().right = right;
                    },
                    None => {
                        self.nodes[parent.id()].item_mut().data =
                            TypedNodeData::Internal(right.unwrap());
                    },
                }
                if let Some(right) = right {
                    self.nodes[right.id()].item_mut().left = left;
                }
            },
            None => {
                self.root = None;
            },
        }
    }

    fn restore_leaf(&mut self, leaf: Leaf) {
        self.leaves[leaf.id()].as_mut().unwrap().restore();
        self.leaf_count += 1;
        let node = self.leaf(leaf);
        match self.parent(node) {
            Some(parent) => {
                if let TypedNodeData::Internal(right) = self.nodes[parent.id()].item().data {
                    self.nodes[right.id()].item_mut().left = Some(node);
                    self.nodes[node.id()].item_mut().right = Some(right);
                    self.nodes[parent.id()].item_mut().data = TypedNodeData::Internal(node);
                }
            },
            None => {
                self.root = Some(node);
            },
        }
    }
}


impl<T> Tree<T> {

    /// Access the node data for the given node
    fn node(&self, node: Node) -> &NodeData<T> {
        self.nodes[node.id()].item()
    }

    /// Access the node data mutably
    fn node_mut(&mut self, node: Node) -> &mut NodeData<T> {
        self.nodes[node.id()].item_mut()
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


impl<'a, T: 'a> Iterator for ChildIter<'a, T> {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        self.child.map(|node| {
            self.child = self.tree.node(node).right;
            node
        })
    }
}


/// Concrete implementation of the `TreeBuilder` trait
pub struct TreeBuilder<T> {

    // The current tree under construction
    current_tree: Option<Tree<T>>,

    // The set of trees already constructed
    trees: Vec<Tree<T>>,

    // Hash map to map labels to leaf IDs to ensure leaves with the same label in different trees
    // get the same ID.
    leaf_ids: HashMap<T, Leaf>,
}


impl<T> traits::TreeBuilder<T> for TreeBuilder<T>
where T: Clone + Eq + Hash {

    type Node = Node;

    type Tree = Tree<T>;

    fn new() -> Self {
        TreeBuilder {
            current_tree: None,
            trees:        vec![],
            leaf_ids:     HashMap::new(),
        }
    }

    fn new_tree(&mut self) {
        self.current_tree = Some(Tree::new());
    }

    fn new_leaf(&mut self, label: T) -> Node {

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
                left:   None,
                right:  None,
                data:   TypedNodeData::Leaf(*leaf, label),
            }));
            t.node_count += 1;
            t.leaf_count += 1;
            node
        }).unwrap()
    }

    fn new_node(&mut self, children: Vec<Node>) -> Node {
        self.current_tree.as_mut().map(|t| {
            let node = Node(t.nodes.len());
            t.nodes.push(Removable::new(NodeData {
                parent: None,
                left:   None,
                right:  None,
                data:   TypedNodeData::Internal(children[0]),
            }));
            let mut last = None;
            for child in children.into_iter() {
                t.node_mut(child).left   = last;
                t.node_mut(child).parent = Some(node);
                if let Some(node) = last {
                    t.node_mut(node).right = Some(child);
                }
                last = Some(child);
            }
            t.node_count += 1;
            node
        }).unwrap()
    }

    fn finish_tree(&mut self, root: Node) {
        self.current_tree.as_mut().map(|t| t.root = Some(root));
        self.trees.push(self.current_tree.take().unwrap());
    }

    fn trees(self) -> Vec<Self::Tree> {
        self.trees
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use super::traits::TreeBuilder as TreeBuilderTrait;

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
        let mut answers0 = vec![true, true, true, true, false, true, false, true, false].into_iter();
        let mut nodes1   = trees[1].nodes();
        let mut answers1 = vec![true, true, true, true, true, false, false, false].into_iter();
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

    /// Test that left and right siblings are reported correctly
    #[test]
    fn build_tree_siblings() {
        let trees       = build_tree();
        let mut nodes0  = trees[0].nodes();
        let mut lefts0  = [
            None, Some(5), Some(0), Some(2), None, None, Some(4), Some(6), None].into_iter();
        let mut rights0 = [
            Some(2), None, Some(3), None, Some(6), Some(1), Some(7), None, None].into_iter();
        let mut nodes1  = trees[1].nodes();
        let mut lefts1  = [
            Some(4), None, Some(6), None, Some(3), Some(1), None, None].into_iter();
        let mut rights1 = [
            None, Some(5), None, Some(4), Some(0), None, Some(2), None].into_iter();
        for _ in 0..9 {
            let node  = nodes0.next().unwrap();
            let left  = lefts0.next().unwrap().map(|id| Node::new(id));
            let right = rights0.next().unwrap().map(|id| Node::new(id));
            assert_eq!(trees[0].left(node), left);
            assert_eq!(trees[0].right(node), right);
        }
        for _ in 0..8 {
            let node  = nodes1.next().unwrap();
            let left  = lefts1.next().unwrap().map(|id| Node::new(id));
            let right = rights1.next().unwrap().map(|id| Node::new(id));
            assert_eq!(trees[1].left(node), left);
            assert_eq!(trees[1].right(node), right);
        }
    }
}
