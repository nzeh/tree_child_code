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
        type Node: Clone + Copy + Id + PartialEq;

        /// The type used to identify leaves
        type Leaf: Clone + Copy + Id + PartialEq;

        /// An iterator over the nodes of the tree
        type NodeIter: Iterator<Item=Self::Node>;

        /// An iterator over the leaves of the tree
        type LeafIter: Iterator<Item=Self::Node>;

        /// An iterator over the children of a node
        type ChildIter: Iterator<Item=Self::Node>;

        /// Create a new tree
        fn new() -> Self;

        /// Access the number of nodes in the tree
        fn node_count(&'a self) -> usize;

        /// Access the root of the next tree
        fn root(&'a self) -> Option<Self::Node>;

        /// Access the nodes of the tree
        fn nodes(&'a self) -> Self::NodeIter;

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
    nodes: Vec<NodeData<T>>,

    /// The root of the tree
    root: Option<Node>,

    /// The set of leaves in the tree
    leaves: Vec<Node>,

    /// Number of nodes in this tree
    node_count: usize,
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
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Node(usize);


/// The type used to refer to leaves
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Leaf(usize);


/// An iterator over the nodes of a tree
pub struct NodeIter {
    node: usize,
    end:  usize,
}

/// An iterator over the leaves of a tree
pub struct LeafIter<'a> {
    iter: slice::Iter<'a, Node>,
}


/// An iterator over the children of a node
pub struct ChildIter<'a, T: 'a> {
    tree:  &'a Tree<T>,
    child: Option<Node>,
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

    type NodeIter = NodeIter;

    type LeafIter = LeafIter<'a>;

    type ChildIter = ChildIter<'a, T>;

    fn new() -> Self {
        Tree {
            nodes:      vec![],
            root:       None,
            leaves:     vec![],
            node_count: 0,
        }
    }

    fn node_count(&self) -> usize {
        self.node_count
    }

    fn root(&self) -> Option<Node> {
        self.root
    }

    fn nodes(&'a self) -> NodeIter {
        NodeIter {
            node: 0,
            end:  self.nodes.len(),
        }
    }

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
        self.leaves[leaf.id()]
    }
}


impl<T> Tree<T> {

    /// Access the node data for the given node
    fn node(&self, node: Node) -> &NodeData<T> {
        &self.nodes[node.id()]
    }

    /// Access the node data mutably
    fn node_mut(&mut self, node: Node) -> &mut NodeData<T> {
        &mut self.nodes[node.id()]
    }

}


impl Iterator for NodeIter {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        if self.node < self.end {
            self.node += 1;
            Some(Node::new(self.node - 1))
        } else {
            None
        }
    }
}


impl<'a> Iterator for LeafIter<'a> {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        self.iter.next().map(|t| *t)
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
}


impl<T> traits::TreeBuilder<T> for TreeBuilder<T> {

    type Node = Node;

    type Tree = Tree<T>;

    fn new() -> Self {
        TreeBuilder {
            current_tree: None,
            trees:        vec![],
        }
    }
    fn new_tree(&mut self) {
        self.current_tree = Some(Tree::new());
    }

    fn new_leaf(&mut self, label: T) -> Node {
        self.current_tree.as_mut().map(|t| {
            let leaf = Leaf(t.leaves.len());
            let node = Node(t.nodes.len());
            t.leaves.push(node);
            t.nodes.push(NodeData {
                parent: None,
                left:   None,
                right:  None,
                data:   TypedNodeData::Leaf(leaf, label),
            });
            t.node_count += 1;
            node
        }).unwrap()
    }

    fn new_node(&mut self, children: Vec<Node>) -> Node {
        self.current_tree.as_mut().map(|t| {
            let node = Node(t.nodes.len());
            t.nodes.push(NodeData {
                parent: None,
                left:   None,
                right:  None,
                data:   TypedNodeData::Internal(children[0]),
            });
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
