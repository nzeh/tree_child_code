use std::ops::Index;
use std::slice;


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


impl<T> Tree<T> {

    /// Create a new tree
    pub fn new() -> Tree<T> {
        Tree {
            nodes:      vec![],
            root:       None,
            leaves:     vec![],
            node_count: 0,
        }
    }

    /// The number of nodes in the tree
    pub fn node_count(&self) -> usize {
        self.node_count
    }

    /// The root node of the tree
    pub fn root(&self) -> Option<Node> {
        self.root
    }

    /// Iterator over the nodes of the tree
    pub fn nodes(&self) -> NodeIter<T> {
        NodeIter { iter: self.nodes.iter() }
    }

    /// Iterator over the leaves of the tree
    pub fn leaves(&self) -> LeafIter<T> {
        LeafIter {
            tree: self,
            iter: self.leaves.iter(),
        }
    }

    /// Iterator over the children of a node
    pub fn children(&self, node: &InternalNodeData) -> ChildIter<T> {
        ChildIter {
            tree:  self,
            child: Some(node.first_child),
        }
    }
}


/// The type used to represent tree nodes
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Node(usize);


impl Node {

    /// Access the ID of this node
    pub fn id(self) -> usize {
        self.0
    }
}


/// Indexing into a tree using a `Node` returns the corresponding node data
impl<T> Index<Node> for Tree<T> {

    type Output = NodeData<T>;

    fn index(&self, index: Node) -> &NodeData<T> {
        &self.nodes[index.id()]
    }
}


#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Leaf(usize);


impl Leaf {

    /// Access the ID of this leaf
    pub fn id(self) -> usize {
        self.0
    }
}


/// Indexing into a tree using a `Leaf` returns the corresponding `Node`
impl<T> Index<Leaf> for Tree<T> {

    type Output = Node;

    fn index(&self, index: Leaf) -> &Node {
        &self.leaves[index.id()]
    }
}


/// The data associated with a node
pub enum NodeData<T> {
    Leaf(LeafData<T>),
    Internal(InternalNodeData),
}


impl<T> NodeData<T> {

    /// Access the parent of the current node
    pub fn parent(&self) -> Option<Node> {
        match self {
            NodeData::Leaf(info)     => info.parent(),
            NodeData::Internal(info) => info.parent(),
        }
    }

    /// Access the left sibling of the current node
    pub fn left(&self) -> Option<Node> {
        match self {
            NodeData::Leaf(info)     => info.left(),
            NodeData::Internal(info) => info.left(),
        }
    }

    /// Access the right sibling of the current node
    pub fn right(&self) -> Option<Node> {
        match self {
            NodeData::Leaf(info)     => info.right(),
            NodeData::Internal(info) => info.right(),
        }
    }
}


/// The info associated with a leaf
pub struct LeafData<T> {

    /// Parent
    parent: Option<Node>,

    /// Left sibling
    left: Option<Node>,

    /// Right sibling
    right: Option<Node>,

    /// The leaf's label
    label: T,

    /// The leaf's ID
    id: Leaf,
}

impl<T> LeafData<T> {

    /// Access the parent of this leaf
    pub fn parent(&self) -> Option<Node> {
        self.parent
    }

    /// Access the left sibling of this leaf
    pub fn left(&self) -> Option<Node> {
        self.left
    }

    /// Access the right sibling of this leaf
    pub fn right(&self) -> Option<Node> {
        self.right
    }

    /// Access the leaf's ID
    pub fn id(&self) -> Leaf {
        self.id
    }
}


/// The info associated with an internal node
pub struct InternalNodeData {

    /// Parent
    parent: Option<Node>,

    /// Left sibling
    left: Option<Node>,

    /// Right sibling
    right: Option<Node>,

    /// The first child of this node
    first_child: Node,
}


impl InternalNodeData {

    /// Access the parent of this internal node
    pub fn parent(&self) -> Option<Node> {
        self.parent
    }

    /// Access the left sibling of this internal node
    pub fn left(&self) -> Option<Node> {
        self.left
    }

    /// Access the right sibling of this internal node
    pub fn right(&self) -> Option<Node> {
        self.right
    }
}


/// An iterator over the nodes of a tree
pub struct NodeIter<'a, T: 'a> {
    iter: slice::Iter<'a, NodeData<T>>,
}


impl<'a, T: 'a> Iterator for NodeIter<'a, T> {

    type Item = &'a NodeData<T>;

    fn next(&mut self) -> Option<&'a NodeData<T>> {
        self.iter.next()
    }
}


/// An iterator over the leaves of a tree
pub struct LeafIter<'a, T: 'a> {
    tree: &'a Tree<T>,
    iter: slice::Iter<'a, Node>,
}


impl <'a, T: 'a> Iterator for LeafIter<'a, T> {

    type Item = &'a LeafData<T>;

    fn next(&mut self) -> Option<&'a LeafData<T>> {
        match self.iter.next() {
            None => None,
            Some(&leaf) => {
                match self.tree[leaf] {
                    NodeData::Leaf(ref data) => Some(data),
                    _                        => None,
                }
            }
        }
    }
}


/// An iterator over the children of a node
pub struct ChildIter<'a, T: 'a> {
    tree:  &'a Tree<T>,
    child: Option<Node>,
}


impl<'a, T: 'a> Iterator for ChildIter<'a, T> {

    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        self.child.map(|node| {
            self.child = self.tree[node].right();
            node
        })
    }
}
