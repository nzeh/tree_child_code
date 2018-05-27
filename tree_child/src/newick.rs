//! A module to parse Newick strings into a tree or forest.  The two main functions are
//! `parse_tree()` and `parse_forest()`.  For `parse_tree()`, the input has to consist of a single
//! line that is a valid Newick string representing a single tree.  For `parse_forest()`, the input
//! has to be a multi-line text.  Each line encodes one of the trees in the forest.
//!
//! These functions take a mutable reference to tree builder as an argument.  This is an object
//! implementing the `Builder` trait.  The parser is implemented purely in terms of the calling
//! the methods of the `Builder` trait.
//!
//! The grammar for a a Newick string used by this parser is the following:
//!
//! ```ignore
//! Newick     -> Tree ;
//! Tree       -> Subtree Label : EdgeLength
//! Label      -> string | Nothing
//! EdgeLength -> number | Nothing
//! Subtree    -> ( Trees ) | Nothing
//! Trees      -> Tree MoreTrees
//! MoreTrees  -> , Trees | Nothing
//! Nothing    ->
//! ```
//!
//! **Important note:** The parser accepts any string that adheres to this grammar, but is simply
//! ignores labels of internal nodes (nodes whose `Subtree` part is not empty) and it completely
//! ignores edge lengths.  This is because edge lengths and labels of internal nodes are irrelevant
//! in the context of computing tree-child hybridization networks.


use tree::traits::{Tree, TreeBuilder};
use std::fmt::Write;
use std::iter;
use std::result;
use std::str;


/// The parser's result type
type Result<T> = result::Result<T, Error>;


/// The error raised when a parse error is encountered
#[derive(Debug)]
pub struct Error {
    message: String,
    pos:     Pos,
}


/// Representation of an input position
#[derive(Clone, Copy, Debug)]
struct Pos(usize, usize);


/// Parse a given one-line Newick string using the given tree builder
pub fn parse_tree<B>(builder: &mut B, newick: &str) -> Result<()>
where B: TreeBuilder<String> {
    Parser::new(builder, newick).parse_tree()
}


/// Parse a given multi-line Newick string using the given tree builder
pub fn parse_forest<B>(builder: &mut B, newick: &str) -> Result<()>
where B: TreeBuilder<String> {
    Parser::new(builder, newick).parse_forest()
}


/// Struct representing the state of the Newick parser
struct Parser<'b, 'i, B: 'b + TreeBuilder<String>> {

    /// The builder used to build the tree
    builder: &'b mut B,

    /// The current input position
    pos: Pos,

    /// The iterator currently used
    chars: iter::Peekable<str::Chars<'i>>,
}

impl<'b, 'i, B> Parser<'b, 'i, B>
where B: 'b + TreeBuilder<String> {

    /// Create a new parser that parses the given Newick string and uses the given builder to
    /// construct the corresponding tree.
    fn new(builder: &'b mut B, newick: &'i str) -> Parser<'b, 'i, B> {
        Parser {
            builder,
            pos:   Pos(1, 1),
            chars: newick.chars().peekable()
        }
    }

    /// Parse a tree from a one-line Newick string
    fn parse_tree(mut self) -> Result<()> {
        self.parse_one_tree()?;
        match self.chars.next() {
            None => Ok(()),
            _    => self.error("expected a one-line input"),
        }
    }

    /// Parse a forest from a multi-line Newick string
    fn parse_forest(mut self) -> Result<()> {
        while self.chars.peek().is_some() {
            self.parse_one_tree()?;
            self.pos = Pos(self.pos.0 + 1, 1);
        }
        Ok(())
    }

    /// Parse a tree from a one-line Newick string.  Does not enforce that the input has just one
    /// line.  This is guaranteed because this function is called by `parse_tree()` or
    /// `parse_forest()`, which pass a single line to this function.
    fn parse_one_tree(&mut self) -> Result<()> {
        self.builder.new_tree();
        let root = self.parse_subtree()?;
        self.parse_symbol(';')?;
        self.skip_spaces();
        self.parse_eol()?;
        self.builder.finish_tree(root);
        Ok(())
    }

    /// Check that we're at the end of the line
    fn parse_eol(&mut self) -> Result<()> {
        let pos = self.pos;
        match self.chars.next() {
            None       => Ok(()),
            Some('\n') => Ok(()),
            _          => {
                self.pos = pos;
                self.error("expected end of line")
            },
        }
    }

    /// Parse the given symbol
    fn parse_symbol(&mut self, sym: char) -> Result<()> {
        let pos = self.pos;
        match self.chars.next() {
            Some(c) if c == sym => Ok(()),
            _ => {
                self.pos = pos;
                self.error(&format!("expected `{}'", sym))
            },
        }
    }

    /// Skip over spaces
    fn skip_spaces(&mut self) {
        loop {
            match self.chars.peek() {
                Some('\n')                    => return,
                Some(&c) if c.is_whitespace() => self.chars.next(),
                _                             => return,
            };
        }
    }

    /// Parse one subtree
    fn parse_subtree(&mut self) -> Result<B::Node> {
        self.skip_spaces();
        match self.chars.peek() {
            Some('(') => {
                self.chars.next();
                let children = self.parse_subtrees()?;
                self.parse_symbol(')')?;
                self.parse_label()?;
                self.skip_edge_length()?;
                Ok(self.builder.new_node(children))
            },
            _ => {
                let label = self.parse_label()?;
                self.skip_edge_length()?;
                Ok(self.builder.new_leaf(label))
            },
        }
    }

    /// Parse a list of subtrees
    fn parse_subtrees(&mut self) -> Result<Vec<B::Node>> {
        let mut nodes = vec![];
        let node = self.parse_subtree()?;
        nodes.push(node);
        loop {
            self.skip_spaces();
            match self.chars.peek() {
                Some(',') => {
                    self.chars.next();
                    let node = self.parse_subtree()?;
                    nodes.push(node);
                },
                _ => break,
            };
        }
        Ok(nodes)
    }

    /// Skip edge lengths
    fn skip_edge_length(&mut self) -> Result<()> {
        self.skip_spaces();
        match self.chars.peek() {
            Some(&c) if c == ':' => (),
            _                    => return Ok(()),
        }
        self.chars.next();
        loop {
            match self.chars.peek() {
                None                            => break,
                Some(&c)                        => match c {
                    ',' | ';' | ':' | '(' | ')' => break,
                    _                           => self.chars.next(),
                },
            };
        }
        Ok(())
    }

    /// Parse a node label
    fn parse_label(&mut self) -> Result<String> {
        let mut label = "".to_string();
        loop {
            match self.chars.peek() {
                None                            => break,
                Some(&c)                        => match c {
                    ',' | ';' | ':' | '(' | ')' => break,
                    _                           => {
                        label.push(c);
                        self.chars.next();
                    },
                },
            }
        }
        Ok(label.trim().to_string())
    }

    /// Report an error at the current position
    fn error<T>(&self, message: &str) -> Result<T> {
        Err(Error {
            message: message.to_string(),
            pos:     self.pos,
        })
    }
}


/// Format a tree into a Newick string
pub fn format_tree<T>(tree: &T) -> Option<String>
where for<'t> T: Tree<'t, String> {
    let mut newick = String::new();
    format_one_tree(tree, &mut newick)?;
    Some(newick)
}


/// Format a forest into a Newick string, one line per tree
pub fn format_forest<T>(forest: &[T]) -> Option<String>
where for<'t> T: Tree<'t, String> {
    let mut newick = String::new();
    for tree in forest {
        format_one_tree(tree, &mut newick)?;
        newick.write_char('\n').unwrap();
    }
    Some(newick)
}


/// Format a tree into a Newick string, held in a given string buffer
fn format_one_tree<T>(tree: &T, newick: &mut String) -> Option<()>
where for<'t> T: Tree<'t, String> {

    fn visit_node<'t, T>(tree: &'t T, newick: &mut String, node: T::Node) -> Option<()>
    where T: 't + Tree<'t, String> {
        if tree.is_leaf(node) {
            newick.write_str(&tree.label(node)?).unwrap();
        } else {
            newick.write_char('(').unwrap();
            let mut children = tree.children(node);
            visit_node(tree, newick, children.next()?);
            for child in children {
                newick.write_char(',').unwrap();
                visit_node(tree, newick, child);
            }
            newick.write_char(')').unwrap();
        }
        Some(())
    };

    if let Some(root) = tree.root() {
        visit_node(tree, newick, root)?;
        newick.write_str(";").unwrap();
        Some(())
    } else {
        None
    }
}


#[cfg(test)]
mod tests {

    use std::slice;
    use super::*;
    use tree::traits::Id;

    /// Representation of a tree in the implementation of these tests
    struct TestTree {

        /// The root of the tree
        root: Option<usize>,

        /// Association list between internal nodes and the lists of their children
        internal_nodes: Vec<(usize, Vec<usize>)>,

        /// Association list between leaves and their leaf IDs and labels
        leaves: Vec<(usize, usize, String)>,
    }

    impl<'a> Tree<'a, String> for TestTree {

        type Node = usize;

        type Leaf = usize;

        type NodeIter = TestNodeIter<'a>;

        type LeafIter = TestLeafIter<'a>;

        type ChildIter = TestChildIter<'a>;

        fn new() -> Self {
            TestTree {
                root:           None,
                internal_nodes: vec![],
                leaves:         vec![],
            }
        }

        fn node_count(&'a self) -> usize {
            self.internal_nodes.len() + self.leaves.len()
        }

        fn root(&'a self) -> Option<usize> {
            self.root
        }

        fn nodes(&'a self) -> TestNodeIter<'a> {
            TestNodeIter {
                internal_nodes: self.internal_nodes.iter(),
                leaves:         self.leaves.iter(),
            }
        }

        fn leaves(&'a self) -> TestLeafIter<'a> {
            TestLeafIter {
                leaves: self.leaves.iter(),
            }
        }

        fn children(&'a self, node: usize) -> TestChildIter<'a> {
            for (parent, children) in self.internal_nodes.iter() {
                if *parent == node {
                    return TestChildIter::HasChildren(children.iter());
                }
            }
            TestChildIter::HasNoChildren
        }

        fn parent(&'a self, node: usize) -> Option<usize> {
            for (parent, children) in self.internal_nodes.iter() {
                for child in children {
                    if *child == node {
                        return Some(*parent);
                    }
                }
            }
            None
        }

        fn left(&'a self, node: usize) -> Option<usize> {
            for (_, children) in self.internal_nodes.iter() {
                let mut last = None;
                for child in children {
                    if *child == node {
                        return last;
                    }
                    last = Some(*child);
                }
            }
            None
        }

        fn right(&'a self, node: usize) -> Option<usize> {
            for (_, children) in self.internal_nodes.iter() {
                let mut last = None;
                for child in children {
                    if last == Some(node) {
                        return Some(*child);
                    }
                    last = Some(*child);
                }
            }
            None
        }

        fn is_leaf(&'a self, node: usize) -> bool {
            for (leaf, _, _) in self.leaves.iter() {
                if *leaf == node {
                    return true;
                }
            }
            false
        }

        fn leaf_id(&'a self, node: usize) -> Option<usize> {
            for (leaf, id, _) in self.leaves.iter() {
                if *leaf == node {
                    return Some(*id);
                }
            }
            None
        }

        fn label(&'a self, node: usize) -> Option<&String> {
            for (leaf, _, label) in self.leaves.iter() {
                if *leaf == node {
                    return Some(label);
                }
            }
            None
        }

        fn leaf(&'a self, leaf: usize) -> usize {
            for (node, id, _) in self.leaves.iter() {
                if leaf == *id {
                    return *node;
                }
            }
            panic!("Trying to retrieve node ID of a non-existent leaf.");
        }
    }

    struct TestNodeIter<'a> {
        internal_nodes: slice::Iter<'a, (usize, Vec<usize>)>,
        leaves: slice::Iter<'a, (usize, usize, String)>,
    }

    impl<'a> Iterator for TestNodeIter<'a> {

        type Item = usize;

        fn next(&mut self) -> Option<usize> {
            match self.internal_nodes.next() {
                Some((node, _)) => Some(*node),
                None            => self.leaves.next().map(|(node, _, _)| *node),
            }
        }
    }

    struct TestLeafIter<'a> {
        leaves: slice::Iter<'a, (usize, usize, String)>,
    }

    impl<'a> Iterator for TestLeafIter<'a> {

        type Item = usize;

        fn next(&mut self) -> Option<usize> {
            self.leaves.next().map(|(node, _, _)| *node)
        }
    }


    enum TestChildIter<'a> {
        HasChildren(slice::Iter<'a, usize>),
        HasNoChildren,
    }

    impl<'a> Iterator for TestChildIter<'a> {

        type Item = usize;

        fn next(&mut self) -> Option<usize> {
            match self {
                TestChildIter::HasNoChildren     => None,
                TestChildIter::HasChildren(iter) => iter.next().map(|node| *node),
            }
        }
    }

    impl Id for usize {

        fn new(id: usize) -> usize {
            id
        }

        fn id(self) -> usize {
            self
        }

    }

    /// Tree builder instance used in these tests
    struct TestTreeBuilder {

        /// The next available node ID
        next_id: usize,

        /// The tree currently under construction
        current_tree: Option<TestTree>,

        /// The list of trees constructed so far
        trees: Vec<TestTree>,
    }

    impl TreeBuilder<String> for TestTreeBuilder {

        type Node = usize;

        type Tree = TestTree;

        fn new() -> Self {
            TestTreeBuilder {
                next_id:      0,
                current_tree: None,
                trees:        vec![],
            }
        }

        fn new_tree(&mut self) {
            self.current_tree = Some(TestTree::new());
        }

        fn new_leaf(&mut self, label: String) -> usize {

            let node_id = self.next_id;
            self.next_id += 1;

            let leaf_id = self.current_tree.as_ref().unwrap().leaves.len();

            self.current_tree.as_mut().unwrap().leaves.push((node_id, leaf_id, label));

            node_id
        }

        fn new_node(&mut self, children: Vec<usize>) -> usize {

            let node_id = self.next_id;
            self.next_id += 1;

            self.current_tree.as_mut().unwrap().internal_nodes.push((node_id, children));

            node_id
        }

        fn finish_tree(&mut self, root: usize) {
            self.current_tree.as_mut().unwrap().root = Some(root);
            self.trees.push(self.current_tree.take().unwrap());
        }

        fn trees(self) -> Vec<TestTree> {
            self.trees
        }
    }

    /// Test that a well-formed one-line Newick string is parsed and formatted correctly.
    #[test]
    fn parse_tree_success() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "(a,foo_bar$:432,((c,  d   )e:12  ,(  f,g,h)i,j));").is_ok());
        let trees = builder.trees();
        assert_eq!(trees.len(), 1);
        let newick = format_tree(&trees[0]).unwrap();
        assert_eq!(newick, "(a,foo_bar$,((c,d),(f,g,h),j));");
    }

    /// Test that a well-formed multi-line Newick string is parsed and formatted correctly.
    #[test]
    fn parse_forest_success() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_forest(&mut builder, "(((a,b),c),(d,e))   ;\nf;\n(g,((h,i),j));").is_ok());
        let trees = builder.trees();
        assert_eq!(trees.len(), 3);
        let newick = format_forest(&trees).unwrap();
        assert_eq!(newick, "(((a,b),c),(d,e));\nf;\n(g,((h,i),j));\n");
    }

    /// Test that parse_tree rejects a multi-line string.
    #[test]
    fn parse_tree_multiline_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "(((a,b),c),(d,e))   ;\nf;\n(g,((h,i),j));").is_err());
    }

    /// Test that parse_tree rejects a string with multiple pairs of top-level parentheses.
    #[test]
    fn parse_tree_missing_root_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c)(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with two semicolons.
    #[test]
    fn parse_tree_two_semicolons_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c);(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with a missing closing parenthesis.
    #[test]
    fn parse_tree_missing_close_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c);(d,(e,f);").is_err());
    }

    /// Test that parse_tree rejects a string with two many closing parentheses.
    #[test]
    fn parse_tree_excess_close_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c));(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with two edge lengths attached to a single node.
    #[test]
    fn parse_tree_two_edge_lengths_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b:34:1),c));(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with multiple pairs of top-level parentheses.
    #[test]
    fn parse_forest_missing_root_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c)(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with two semicolons.
    #[test]
    fn parse_forest_two_semicolons_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c);(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with a missing closing parenthesis.
    #[test]
    fn parse_forest_missing_close_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c);(d,(e,f);").is_err());
    }

    /// Test that parse_forest rejects a string with two many closing parentheses.
    #[test]
    fn parse_forest_excess_close_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c));(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with two edge lengths attached to a single node.
    #[test]
    fn parse_forest_two_edge_lengths_failure() {
        let mut builder = TestTreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b:34:1),c));(d,(e,f));").is_err());
    }
}
