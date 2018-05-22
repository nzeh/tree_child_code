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


use tree::{Builder, Accessor};
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
pub fn parse_tree<B: Builder<String>>(builder: &mut B, newick: &str) -> Result<()> {
    Parser::new(builder, newick).parse_tree()
}


/// Parse a given multi-line Newick string using the given tree builder
pub fn parse_forest<B: Builder<String>>(builder: &mut B, newick: &str) -> Result<()> {
    Parser::new(builder, newick).parse_forest()
}


/// Struct representing the state of the Newick parser
struct Parser<'b, 'i, B: 'b + Builder<String>> {

    /// The builder used to build the tree
    builder: &'b mut B,

    /// The current input position
    pos: Pos,

    /// The iterator currently used
    chars: iter::Peekable<str::Chars<'i>>,
}

impl<'b, 'i, B: 'b + Builder<String>> Parser<'b, 'i, B> {

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


/// Format a tree or forest into a Newick string
pub fn format<R: Accessor<String>>(reader: &mut R) -> Option<String>  {
    let mut newick = String::new();

    fn visit_node<R: Accessor<String>>(reader: &mut R, newick: &mut String, node: R::Node) -> Option<()> {
        if reader.is_leaf(node) {
            newick.write_str(&reader.label(node)?).unwrap();
        } else {
            newick.write_char('(').unwrap();
            let mut children = reader.children(node);
            visit_node(reader, newick, children.next()?);
            for child in children {
                newick.write_char(',').unwrap();
                visit_node(reader, newick, child);
            }
            newick.write_char(')').unwrap();
        }
        Some(())
    };

    while let Some(root) = reader.root() {
        visit_node(reader, &mut newick, root)?;
        newick.write_str(";\n").unwrap();
    }

    if newick.is_empty() {
        None
    } else {
        Some(newick)
    }
}


#[cfg(test)]
mod tests {

    use std::iter::Sum;
    use std::vec;
    use super::*;

    /// Representation of a tree in the implementation of these tests
    struct Tree {

        /// The root of the tree
        root: usize,

        /// Association list between internal nodes and the lists of their children
        internal_nodes: Vec<(usize, Vec<usize>)>,

        /// Association list between leaves and their labels
        leaves: Vec<(usize, String)>,
    }

    impl Tree {

        ///  Create a new empty tree
        fn new() -> Tree {
            Tree {
                root:           0,
                internal_nodes: vec![],
                leaves:         vec![],
            }
        }
    }

    /// Tree builder instance used in these tests
    struct TestBuilder {

        /// The next available node ID
        node_id: usize,

        /// The tree currently under construction
        current_tree: Option<Tree>,

        /// The list of trees constructed so far
        trees: Vec<Tree>,
    }

    impl TestBuilder {

        /// Create a new `TestBuilder`
        fn new() -> TestBuilder {
            TestBuilder {
                node_id:      0,
                current_tree: None,
                trees:        vec![],
            }
        }
    }

    impl Builder for TestBuilder {
        
        type Node = usize;

        fn new_tree(&mut self) {
            self.current_tree = Some(Tree::new());
        }

        fn new_leaf(&mut self, label: String) -> Self::Node {
            let node_id = self.node_id;
            self.node_id += 1;
            self.current_tree.as_mut().map(
                |tree| tree.leaves.push((node_id, label)));
            node_id
        }

        fn new_node(&mut self, children: Vec<Self::Node>) -> Self::Node {
            let node_id = self.node_id;
            self.node_id += 1;
            self.current_tree.as_mut().map(
                |tree| tree.internal_nodes.push((node_id, children)));
            node_id
        }

        fn finish_tree(&mut self, root: Self::Node) {
            self.current_tree.as_mut().map(
                |tree| tree.root = root);
            self.trees.push(self.current_tree.take().unwrap());
        }
    }

    /// The tree accessor used in these tests
    struct TestAccessor {
        roots:    vec::IntoIter<usize>,
        parents:  Vec<Option<usize>>,
        labels:   Vec<Option<String>>,
    }

    impl TestAccessor {

        /// Create a new tree accessor from a forest represented as a list of trees
        fn new(trees: Vec<Tree>) -> TestAccessor {

            // The number of nodes in the tree is just the number of leaves plus the number of
            // internal nodes, summed over all trees in the forest.
            let num_nodes = usize::sum(trees.iter().map(
                    |t| t.internal_nodes.len() + t.leaves.len()
            ));

            // Allocate vectors to store the parents of nodes and the labels of nodes, initially
            // `None` for every node.
            let mut parents = vec![None; num_nodes];
            let mut labels  = vec![None; num_nodes];

            // Construct an iterator over the tree roots
            let roots = trees.iter().map(|t| t.root).collect::<Vec<usize>>().into_iter();

            // Populate the `parents` and `labels` vectors
            for t in trees {
                for (node, children) in t.internal_nodes {
                    for child in children {
                        parents[child] = Some(node);
                    }
                }
                for (node, label) in t.leaves {
                    labels[node] = Some(label);
                }
            }

            TestAccessor { roots, parents, labels }
        }
    }

    impl Accessor for TestAccessor {
        
        type Node = usize;

        type Children = vec::IntoIter<usize>;

        fn root(&mut self) -> Option<usize> {
            self.roots.next()
        }

        fn label(&self, node: Self::Node) -> Option<&str> {
            self.labels[node].as_ref().map(|s| s.as_str())
        }

        fn children(&self, node: Self::Node) -> Self::Children {
            let mut children = vec![];
            for child in 0..self.parents.len() {
                if self.parents[child] == Some(node) {
                    children.push(child);
                }
            }
            children.into_iter()
        }

        fn is_leaf(&self, node: Self::Node) -> bool {
            self.labels[node].is_some()
        }
    }

    // Correct rejection of ill-formed input by parse_forest
    // - Two top-level parentheses
    // - ; not at end of line
    // - Two many opening parentheses
    // - Two many closing parentheses
    // - Two colons

    /// Test that a well-formed one-line Newick string is parsed and formatted correctly.
    #[test]
    fn parse_tree_success() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "(a,foo_bar$:432,((c,  d   )e:12  ,(  f,g,h)i,j));").is_ok());
        let mut acc = TestAccessor::new(builder.trees);
        let newick = format(&mut acc).unwrap();
        assert_eq!(newick, "(a,foo_bar$,((c,d),(f,g,h),j));\n");
    }

    /// Test that a well-formed multi-line Newick string is parsed and formatted correctly.
    #[test]
    fn parse_forest_success() {
        let mut builder = TestBuilder::new();
        assert!(parse_forest(&mut builder, "(((a,b),c),(d,e))   ;\nf;\n(g,((h,i),j));").is_ok());
        let mut acc = TestAccessor::new(builder.trees);
        let newick = format(&mut acc).unwrap();
        assert_eq!(newick, "(((a,b),c),(d,e));\nf;\n(g,((h,i),j));\n");
    }

    /// Test that parse_tree rejects a multi-line string.
    #[test]
    fn parse_tree_multiline_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "(((a,b),c),(d,e))   ;\nf;\n(g,((h,i),j));").is_err());
    }

    /// Test that parse_tree rejects a string with multiple pairs of top-level parentheses.
    #[test]
    fn parse_tree_missing_root_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c)(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with two semicolons.
    #[test]
    fn parse_tree_two_semicolons_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c);(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with a missing closing parenthesis.
    #[test]
    fn parse_tree_missing_close_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c);(d,(e,f);").is_err());
    }

    /// Test that parse_tree rejects a string with two many closing parentheses.
    #[test]
    fn parse_tree_excess_close_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c));(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with two edge lengths attached to a single node.
    #[test]
    fn parse_tree_two_edge_lengths_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b:34:1),c));(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with multiple pairs of top-level parentheses.
    #[test]
    fn parse_forest_missing_root_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c)(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with two semicolons.
    #[test]
    fn parse_forest_two_semicolons_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c);(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with a missing closing parenthesis.
    #[test]
    fn parse_forest_missing_close_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c);(d,(e,f);").is_err());
    }

    /// Test that parse_forest rejects a string with two many closing parentheses.
    #[test]
    fn parse_forest_excess_close_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c));(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with two edge lengths attached to a single node.
    #[test]
    fn parse_forest_two_edge_lengths_failure() {
        let mut builder = TestBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b:34:1),c));(d,(e,f));").is_err());
    }
}
