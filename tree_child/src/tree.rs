extern crate slab;

use std::cell::RefCell;
use std::ops::Index;
use std::rc::Rc;

/// A node pool to be shared by multiple trees
pub struct NodePool {
    pool: Rc<RefCell<slab::Slab<Info>>>,
}

/// A phylogenetic tree whose leaves have `usize` labels
pub struct Tree<T> {
    /// The set of nodes in the tree
    nodes: slab::Slab<Info>,

    /// The set of leaves in the tree
    leaves: Vec<Node>,

    /// The leaf labels
    labels: Vec<T>,

    /// The root of the tree
    root: Option<Node>,
}

impl<T> Tree<T> {
    /// The number of nodes in this tree
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// The root node of this tree
    pub fn root(&self) -> Option<Node> {
        self.root
    }

    /// Iterator over the children of a node
    pub fn children(&self, info: &InternalInfo) -> ChildIter<T> {
        ChildIter {
            tree: self,
            child: Some(info.first_child),
        }
    }
}

/// The type used to represent tree nodes
#[derive(Clone, Copy)]
pub struct Node(usize);

impl Node {
    /// Access the ID of this node
    pub fn id(&self) -> usize {
        self.0
    }
}

/// Indexing into a tree using a Node returns the corresponding node info
impl<T> Index<Node> for Tree<T> {
    type Output = Info;
    fn index(&self, index: Node) -> &Info {
        &self.nodes[index.id()]
    }
}

/// The type used to represent tree leaves
#[derive(Clone, Copy)]
pub struct Leaf(usize);

impl Leaf {
    /// Access the ID of this node
    pub fn id(&self) -> usize {
        self.0
    }
}

/// Indexing into a tree using a Leaf returns the corresponding node
impl<T> Index<Leaf> for Tree<T> {
    type Output = Node;
    fn index(&self, index: Leaf) -> &Node {
        &self.leaves[index.id()]
    }
}

/// The info associated with a node
pub enum Info {
    Leaf(LeafInfo),
    Internal(InternalInfo),
}

impl Info {
    /// Access the parent of the current node
    pub fn parent(&self) -> Option<Node> {
        match self {
            Info::Leaf(info) => info.parent(),
            Info::Internal(info) => info.parent(),
        }
    }

    /// Access the left sibling of the current node
    pub fn left(&self) -> Option<Node> {
        match self {
            Info::Leaf(info) => info.left(),
            Info::Internal(info) => info.left(),
        }
    }

    /// Access the right sibling of the current node
    pub fn right(&self) -> Option<Node> {
        match self {
            Info::Leaf(info) => info.right(),
            Info::Internal(info) => info.right(),
        }
    }
}

/// The info associated with a leaf
pub struct LeafInfo {
    /// Parent
    parent: Option<Node>,

    /// Left sibling
    left: Option<Node>,

    /// Right sibling
    right: Option<Node>,

    /// The leaf's ID
    id: Leaf,
}

impl LeafInfo {
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
}

/// The info associated with an internal node
pub struct InternalInfo {
    /// Parent
    parent: Option<Node>,

    /// Left sibling
    left: Option<Node>,

    /// Right sibling
    right: Option<Node>,

    /// The first child of this node
    first_child: Node,
}

impl InternalInfo {
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

/// An iterator over the children of a node
pub struct ChildIter<'a, T: 'a> {
    tree: &'a Tree<T>,
    child: Option<Node>,
}

impl<'a, T: 'a> Iterator for ChildIter<'a, T> {
    type Item = Node;
    fn next(&mut self) -> Option<Node> {
        match self.child {
            None => None,
            Some(node) => {
                self.child = self.tree[node].right();
                Some(node)
            }
        }
    }
}

//impl Tree {
//
//    /// Create a new tree
//    pub fn new() -> Tree {
//        Tree {
//            nodes: slab::Slab::new(),
//            root:  None,
//        }
//    }
//
//    /// Create a new leaf with the given label
//    fn new_leaf(&mut self, label: usize) -> Node {
//        Node(self.nodes.insert(
//                NodeRep::new(NodeData::Leaf(label))))
//    }
//
//    /// Create a new internal node with the given list of children
//    fn new_internal(&mut self, children: Vec<Node>) -> Node {
//
//        let mut iter = children.into_iter();
//        let mut last = iter.next().unwrap();
//
//        let parent = Node(self.nodes.insert(
//                NodeRep::new(NodeData::Internal(last))));
//
//        {
//            let last = self.get_mut(last);
//            last.left   = None;
//            last.parent = Some(parent);
//        }
//
//        for child in iter {
//            {
//                let child = self.get_mut(child);
//                child.left   = Some(last);
//                child.parent = Some(parent);
//            }
//            self.get_mut(last).right = Some(child);
//            last = child;
//        }
//        self.get_mut(last).right = None;
//
//        parent
//    }
//
//    /// Make the given node the root of the tree
//    fn set_root(&mut self, root: Node) {
//        self.root = Some(root)
//    }
//
//    /// Get a shared reference to a node from its ID
//    fn get(&self, node: Node) -> &NodeRep {
//        &self.nodes[node.0]
//    }
//
//    /// Get a mutable reference to a node from its ID
//    fn get_mut(&mut self, node: Node) -> &mut NodeRep {
//        &mut self.nodes[node.0]
//    }
//
////     /// Prune the subtree rooted in the given node from the tree
////     pub fn prune(&mut self, node: Node) -> TreeOp {
////         let (parent, remop) = self.remove_from_parent(node);
////         match parent {
////             Some(p) => {
////                 match self.try_suppress(p) {
////                     Some(suppop) => CompoundOp(vec![remop, suppop]),
////                     _            => remop,
////                 }
////             },
////             _ => remop,
////         }
////     }
////
////     /// Replace the subtree rooted in the first node with a subtree rooted
////     /// in the second node
////     pub fn replace(&mut self, from: Node, to: Node) -> TreeOp {
////         let left   = self.left(from);
////         let right  = self.right(from);
////         let parent = self.parent(from);
////
////         self.set_parent(to, parent);
////         if parent == None {
////             self.root = to;
////         }
////
////         self.set_left(to, left);
////         if let Some(l) = left {
////             self.set_right(l, Some(to));
////         } else if Some(p) = parent {
////             self.set_first_child(p, Some(to));
////         }
////
////         self.set_right(to, right);
////         if let Some(r) = right {
////             self.set_left(r, Some(to));
////         }
////
////         ReplaceOp(from, left, right, parent)
////     }
////
////     /// Split the parent edge of the given node
////     pub fn split(&mut self, node: Node) -> (Node, TreeOp) {
////         let new_parent =
////         match self.parent(node) {
////         }
////         SplitOp(node)
////     }
////
////     /// Contract the parent edge of the given node
////     pub fn contract(&mut self, node: Node) -> TreeOp {
////     }
////
////     /// Resolve the given subset of nodes.  They must all have the same
////     /// parent and must be given in the same order as they appear as
////     /// children of the parent.
////     pub fn resolve(&mut self, nodes: &[Node]) -> (Option<Node>, TreeOp) {
////     }
////
////     /// The parent of the given node
////     pub fn parent(&self, node: Node) -> Option<Node> {
////     }
////
////     /// The left sibling of the given node
////     pub fn left(&self, node: Node) -> Option<Node> {
////     }
////
////     /// The right sibling of the given node
////     pub fn right(&self, node: Node) -> Option<Node> {
////     }
////
////     /// The first child of the given node
////     pub fn first_child(&self, node: Node) -> Option<Node> {
////     }
////
////     /// The label of this node, if it's a leaf
////     pub fn label(&self, node: Node) -> Option<usize> {
////     }
////
////     /// Is the current node a leaf?
////     pub fn is_leaf(&self, node: Node) -> bool {
////     }
////
////     /// Is the current node an internal node?
////     pub fn is_internal(&self, node: Node) -> bool {
////     }
////
////     /// Is the current node the root?
////     pub fn is_root(&self, node: Node) -> bool {
////     }
////
////     /// Is the current node the leftmost child of its parent?
////     pub fn is_left(&self, node: Node) -> bool {
////     }
////
////     /// Is the current node the rightmost child of its parent?
////     pub fn is_right(&self, node: Node) -> bool {
////     }
//}

///// Builder to construct a tree
//pub struct TreeBuilder {
//
//    /// The set of leaf labels
//    leaf_labels: Vec<String>,
//
//    /// Map from leaf label back to its ID (needed to ensure that
//    /// leaves with the same label but in different trees get the
//    /// same ID).
//    leaf_ids: HashMap<String, usize>,
//
//    /// The nodes for the current tree
//    current_tree: Option<Tree>,
//
//    /// The trees built so far
//    trees: Vec<Tree>,
//}

//impl TreeBuilder {
//
//    pub fn new() -> TreeBuilder {
//        TreeBuilder {
//            leaf_labels:  Vec::new(),
//            leaf_ids:     HashMap::new(),
//            current_tree: None,
//            trees:        Vec::new(),
//        }
//    }
//}
//
//impl newick::TreeBuilder for TreeBuilder {
//
//    type Node = Node;
//
//    fn new_tree(&mut self) {
//        self.current_tree = Some(Tree::new());
//    }
//
//    fn new_leaf(&mut self, label: String) -> Self::Node {
//        let leaf_id = *self.leaf_ids.entry(label.clone()).or_insert({
//            let leaf_id = self.leaf_labels.len();
//            self.leaf_labels.push(label);
//            leaf_id
//        });
//        self.current_tree.as_mut().unwrap().new_leaf(leaf_id)
//    }
//
//    fn new_node(&mut self, children: Vec<Self::Node>) -> Self::Node {
//        self.current_tree.as_mut().unwrap().new_internal(children)
//    }
//
//    fn finish_tree(&mut self, root: Self::Node) {
//        self.current_tree.as_mut().unwrap().set_root(root);
//        self.trees.push(self.current_tree.take().unwrap());
//    }
//}
