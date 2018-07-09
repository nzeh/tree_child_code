//! A module to parse Newick strings into a tree or forest and to convert a tree of forest back to
//! a Newick string.
//!
//! # Parsing
//!
//! The two main parsing functions are `parse_tree()` and `parse_forest()`.  For `parse_tree()`,
//! the input has to consist of a single line that is a valid Newick string representing a single
//! tree.  For `parse_forest()`, the input has to be a multi-line text.  Each line encodes one of
//! the trees in the forest.
//!
//! These functions take a mutable reference to a `tree::TreeBuilder` as their first argument.
//! A `tree::TreeBuilder` implements the construction of the tree or forest based on the methods
//! the Newick parser calls.
//!
//! The grammar for a a Newick string used by the parser is the following:
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
//! **Important note:** The parser accepts any string that adheres to this grammar, but it simply
//! ignores labels of internal nodes (nodes whose `Subtree` part is not empty) and it completely
//! ignores edge lengths.  This is because edge lengths and labels of internal nodes are irrelevant
//! in the context of computing tree-child hybridization networks.
//!
//! # Formatting
//!
//! The two main formatting functions are `format_tree()` and `format_forest()'.  They take a
//! `tree::Tree` or `Vec<tree::Tree>` as argument and return a Newick string representing this tree
//! or forest.  In the case of `format_forest()`, each tree is placed on its own line in the output
//! string.

use network::TcNet;
use tree::{Node, Tree, TreeBuilder};
use std::error;
use std::fmt;
use std::fmt::{Display, Write};
use std::hash::Hash;
use std::iter;
use std::result;
use std::str;

/// The parser's result type
type Result<T> = result::Result<T, Error>;

/// The error raised when a parse error is encountered
#[derive(Debug)]
pub struct Error {

    /// The error message
    message: String,

    /// The position in the input text where the error occurred
    pos: Pos,
}

/// Representation of an input position
#[derive(Clone, Copy, Debug)]
struct Pos(usize, usize);

/// Parse a given one-line Newick string using the given tree builder
///
/// # Example
///
/// ```
/// # use tree_child::tree;
/// # use tree_child::newick::*;
/// let newick      = "((a,(b,(c,d))),e);";
/// let mut builder = tree::TreeBuilder::new();
/// parse_tree(&mut builder, newick).unwrap();
/// let tree = &builder.trees()[0];
/// assert_eq!(newick, format_tree(tree).unwrap());
/// ```
pub fn parse_tree(builder: &mut TreeBuilder<String>, newick: &str) -> Result<()> {
    Parser::new(builder, newick).parse_tree()
}

/// Parse a given multi-line Newick string using the given tree builder
///
/// # Example
///
/// ```
/// # use tree_child::tree;
/// # use tree_child::newick::*;
/// let newick      = "((a,(b,(c,d))),e);\n(a,(((b,c),d),e));\n";
/// let mut builder = tree::TreeBuilder::new();
/// parse_forest(&mut builder, newick).unwrap();
/// let forest = builder.trees();
/// assert_eq!(newick, format_forest(&forest).unwrap());
/// ```
pub fn parse_forest(builder: &mut TreeBuilder<String>, newick: &str) -> Result<()> {
    Parser::new(builder, newick).parse_forest()
}

/// Struct representing the state of the Newick parser
struct Parser<'b, 'i> {

    /// The builder used to build the tree
    builder: &'b mut TreeBuilder<String>,

    /// The current input position
    pos: Pos,

    /// The iterator currently used
    chars: iter::Peekable<str::Chars<'i>>,
}

impl<'b, 'i> Parser<'b, 'i> {

    /// Create a new parser that parses the given Newick string and uses the given builder to
    /// construct the corresponding tree.
    fn new(builder: &'b mut TreeBuilder<String>, newick: &'i str) -> Parser<'b, 'i> {
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
            _    => Self::error("expected a one-line input", self.pos),
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
            _          => Self::error("expected end of line", pos),
        }
    }

    /// Parse the given symbol
    fn parse_symbol(&mut self, sym: char) -> Result<()> {
        let pos = self.pos;
        match self.chars.next() {
            Some(c) if c == sym => Ok(()),
            _                   => Self::error(&format!("expected `{}'", sym), pos),
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
    fn parse_subtree(&mut self) -> Result<Node> {
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
    fn parse_subtrees(&mut self) -> Result<Vec<Node>> {

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
    fn error<T>(message: &str, pos: Pos) -> Result<T> {
        Err(Error {
            message: message.to_string(),
            pos,
        })
    }
}

/// Format a tree into a Newick string
///
/// # Example
///
/// ```
/// # use tree_child::tree;
/// # use tree_child::newick::*;
/// let newick      = "((a,(b,(c,d))),e);";
/// let mut builder = tree::TreeBuilder::new();
/// parse_tree(&mut builder, newick).unwrap();
/// let tree = &builder.trees()[0];
/// assert_eq!(newick, format_tree(tree).unwrap());
/// ```
pub fn format_tree<T: Clone + Display>(tree: &Tree<T>) -> Option<String> {
    let leaf_annotator = |_, string| string;
    let node_annotator = |_| "".to_string();
    Formatter::new(tree, leaf_annotator, node_annotator).run()
}

/// Format a forest into a Newick string, one line per tree.
///
/// # Example
///
/// ```
/// # use tree_child::tree;
/// # use tree_child::newick::*;
/// let newick      = "((a,(b,(c,d))),e);\n(a,(((b,c),d),e));\n";
/// let mut builder = tree::TreeBuilder::new();
/// parse_forest(&mut builder, newick).unwrap();
/// let forest = builder.trees();
/// assert_eq!(newick, format_forest(&forest).unwrap());
/// ```
pub fn format_forest<T: Clone + Display>(forest: &[Tree<T>]) -> Option<String> {
    let mut newick = String::new();
    let leaf_annotator = |_, string| string;
    let node_annotator = |_| "".to_string();
    for tree in forest {
        let tree = Formatter::new(tree, leaf_annotator, node_annotator).run()?;
        write!(newick, "{}\n", tree).unwrap();
    }
    Some(newick)
}

/// Format a network into an extended Newick string
pub fn format_network<T>(network: &TcNet<T>) -> Option<String>
where T: Clone + Default + Display + Eq + Hash
{
    let leaf_annotator = |node, string| {
        if let Some(ret) = network.reticulations().get(&node) {
            format!("#H{}", ret)
        } else {
            string
        }
    };

    let node_annotator = |node| {
        if let Some(ret) = network.reticulations().get(&node) {
            format!("#H{}", ret)
        } else {
            "".to_string()
        }
    };

    Formatter::new(network.tree(), leaf_annotator, node_annotator).run()
}

/// The state of the formatting process
struct Formatter<'a, T: 'a, LeafAnnotator, NodeAnnotator> {

    /// The tree being annotated
    tree: &'a Tree<T>,

    /// The current string
    newick: String,
    
    /// An annotator for leaves
    leaf_annotator: LeafAnnotator,

    /// An annotator for internal nodes
    node_annotator: NodeAnnotator,
}

impl<'a, T, LeafAnnotator, NodeAnnotator> Formatter<'a, T, LeafAnnotator, NodeAnnotator>
where T:             'a + Clone + Display,
      LeafAnnotator: Fn(Node, String) -> String,
      NodeAnnotator: Fn(Node) -> String
{
    /// Create a new formatter using the given pair of annotators
    fn new(tree: &'a Tree<T>, leaf_annotator: LeafAnnotator, node_annotator: NodeAnnotator) -> Self {
        Self {
            tree,
            newick: String::new(),
            leaf_annotator,
            node_annotator,
        }
    }

    /// Format a tree into a Newick string, held in a given string buffer
    fn run(mut self) -> Option<String> {

        if let Some(root) = self.tree.root() {
            self.visit_node(root)?;
            self.newick.write_str(";").unwrap();
            Some(self.newick)
        } else {
            None
        }
    }

    /// Visit the given node
    fn visit_node(&mut self, node: Node) -> Option<()> {
        if self.tree.is_leaf(node) {
            write!(self.newick, "{}",
                   (self.leaf_annotator)(node, format!("{}", self.tree.label(node)?))).unwrap();
        } else {
            self.newick.write_char('(').unwrap();
            let mut children = self.tree.children(node);
            self.visit_node(children.next()?);
            for child in children {
                self.newick.write_char(',').unwrap();
                self.visit_node(child);
            }
            self.newick.write_char(')').unwrap();
            write!(self.newick, "{}", (self.node_annotator)(node)).unwrap();
        }
        Some(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    /// Test that a well-formed one-line Newick string is parsed and formatted correctly.
    #[test]
    fn parse_tree_success() {
        let mut builder = TreeBuilder::new();
        assert!(
            parse_tree(&mut builder, "(a,foo_bar$:432,((c,  d   )e:12  ,(  f,g,h)i,j));").is_ok());
        let trees = builder.trees();
        assert_eq!(trees.len(), 1);
        let newick = format_tree(&trees[0]).unwrap();
        assert_eq!(newick, "(a,foo_bar$,((c,d),(f,g,h),j));");
    }

    /// Test that a well-formed multi-line Newick string is parsed and formatted correctly.
    #[test]
    fn parse_forest_success() {
        let mut builder = TreeBuilder::new();
        assert!(parse_forest(&mut builder, "(((a,b),c),(d,e))   ;\nf;\n(g,((h,i),j));").is_ok());
        let trees = builder.trees();
        assert_eq!(trees.len(), 3);
        let newick = format_forest(&trees).unwrap();
        assert_eq!(newick, "(((a,b),c),(d,e));\nf;\n(g,((h,i),j));\n");
    }

    /// Test that parse_tree rejects a multi-line string.
    #[test]
    fn parse_tree_multiline_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_tree(&mut builder, "(((a,b),c),(d,e))   ;\nf;\n(g,((h,i),j));").is_err());
    }

    /// Test that parse_tree rejects a string with multiple pairs of top-level parentheses.
    #[test]
    fn parse_tree_missing_root_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c)(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with two semicolons.
    #[test]
    fn parse_tree_two_semicolons_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c);(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with a missing closing parenthesis.
    #[test]
    fn parse_tree_missing_close_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c);(d,(e,f);").is_err());
    }

    /// Test that parse_tree rejects a string with two many closing parentheses.
    #[test]
    fn parse_tree_excess_close_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b),c));(d,(e,f));").is_err());
    }

    /// Test that parse_tree rejects a string with two edge lengths attached to a single node.
    #[test]
    fn parse_tree_two_edge_lengths_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_tree(&mut builder, "((a,b:34:1),c));(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with multiple pairs of top-level parentheses.
    #[test]
    fn parse_forest_missing_root_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c)(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with two semicolons.
    #[test]
    fn parse_forest_two_semicolons_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c);(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with a missing closing parenthesis.
    #[test]
    fn parse_forest_missing_close_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c);(d,(e,f);").is_err());
    }

    /// Test that parse_forest rejects a string with two many closing parentheses.
    #[test]
    fn parse_forest_excess_close_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b),c));(d,(e,f));").is_err());
    }

    /// Test that parse_forest rejects a string with two edge lengths attached to a single node.
    #[test]
    fn parse_forest_two_edge_lengths_failure() {
        let mut builder = TreeBuilder::new();
        assert!(parse_forest(&mut builder, "((a,b:34:1),c));(d,(e,f));").is_err());
    }
}

impl error::Error for Error {

    fn description(&self) -> &str {
        "Newick parse error"
    }
}

impl fmt::Display for Error {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at position {}", self.message, self.pos)
    }
}

impl fmt::Display for Pos {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}
