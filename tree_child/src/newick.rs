use std::iter;
use std::result;
use std::str;

/// A trait of any structure that can be used to build a tree
pub trait TreeBuilder {

    /// The node type for the tree
    type Node;

    /// Allocate a new tree
    fn new_tree(&mut self);

    /// Create a new leaf in the current tree
    fn new_leaf(&mut self, label: String) -> Self::Node;

    /// Create a new internal node with the given set of children in the current tree.
    fn new_node(&mut self, children: Vec<Self::Node>) -> Self::Node;

    /// Finish the construction of this tree and make the given node its root.
    fn finish_tree(&mut self, root: Self::Node);
}

/// Newick parser struct
pub struct Parser<'b, 'i, Bld: 'b + TreeBuilder> {

    /// The builder used to build the tree
    b: &'b mut Bld,

    /// The current input position
    pos: Pos,
    

    /// The iterator currently used
    chars: iter::Peekable<str::Chars<'i>>,
}

/// The error raised when a parse error is encountered
#[derive(Debug)]
pub struct Error {
    message: String,
    pos:     Pos,
}

/// Parse result
type Result<T> = result::Result<T, Error>;

/// Position
#[derive(Clone, Copy, Debug)]
struct Pos(usize, usize);

impl<'b, 'i, Bld: 'b + TreeBuilder> Parser<'b, 'i, Bld> {

    /// Create a new parser that uses the given builder
    pub fn new(b: &'b mut Bld) -> Parser<'b, 'i, Bld> {
        Parser { b, pos: Pos(1, 1), chars: "".chars().peekable() }
    }

    /// Function to parse a Newick string into a single tree
    pub fn parse_tree(&mut self, newick: &'i str) -> Result<()> {
        self.pos = Pos(1, 1);
        self.chars = newick.chars().peekable();
        self.parse_one_tree()
    }

    /// Function to parse a collection of Newick strings into a set of trees
    pub fn parse_forest(&mut self, newick: &'i str) -> Result<()> {
        for (line, chars) in newick.lines().enumerate() {
            self.pos = Pos(line, 1);
            self.chars = chars.chars().peekable();
            self.parse_one_tree()?;
        }
        Ok(())
    }

    /// Parse one tree
    fn parse_one_tree(&mut self) -> Result<()> {
        self.b.new_tree();
        let root = self.parse_subtree()?;
        self.parse_symbol(';')?;
        self.skip_spaces();
        self.parse_eol()?;
        self.b.finish_tree(root);
        Ok(())
    }

    /// Check that we're at the end of the line
    fn parse_eol(&mut self) -> Result<()> {
        match self.chars.peek() {
            None => Ok(()),
            _    => self.error("expected end of line"),
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
            match self.chars.peek().map(|c| *c) {
                Some(c) if c.is_whitespace() => self.chars.next(),
                _                            => return,
            };
        }
    }

    /// Parse one subtree
    fn parse_subtree(&mut self) -> Result<Bld::Node> {
        self.skip_spaces();
        match self.chars.peek().map(|c| *c) {
            Some('(') => {
                self.chars.next();
                let children = self.parse_subtrees()?;
                self.parse_symbol(')')?;
                self.parse_label()?;
                self.skip_edge_length()?;
                Ok(self.b.new_node(children))
            },
            _ => {
                let label = self.parse_label()?;
                self.skip_edge_length()?;
                Ok(self.b.new_leaf(label))
            },
        }
    }

    /// Parse a list of subtrees
    fn parse_subtrees(&mut self) -> Result<Vec<Bld::Node>> {
        let mut nodes = vec![];
        let node = self.parse_subtree()?;
        nodes.push(node);
        loop {
            self.skip_spaces();
            match self.chars.peek().map(|c| *c) {
                Some(',') => {
                    self.chars.next();
                    let node = self.parse_subtree()?;
                    nodes.push(node);
                },
                _ => break,
            }
        }
        Ok(nodes)
    }

    /// Skip edge lengths
    fn skip_edge_length(&mut self) -> Result<()> {
        self.skip_spaces();
        match self.chars.peek().map(|c| *c) {
            Some(c) if c == ':' => (),
            _                   => return Ok(()),
        }
        self.chars.next();
        loop {
            match self.chars.peek().map(|c| *c) {
                None                           => break,
                Some(c) if ",;:()".contains(c) => break,
                _                              => self.chars.next(),
            };
        }
        Ok(())
    }

    /// Parse a node label
    fn parse_label(&mut self) -> Result<String> {
        let mut label = "".to_string();
        loop {
            match self.chars.peek().map(|c| *c) {
                None => break,
                Some(c) => {
                    if ",;:()".contains(c) {
                        break
                    } else {
                        self.chars.next();
                        label.push(c);
                    }
                },
            };
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

#[cfg(test)]
mod tests {

    use super::*;
    use std::fs::File;
    use std::io::BufRead;
    use std::io::BufReader;

    pub struct TestBuilder {
        node_id: usize,
    }

    impl TreeBuilder for TestBuilder {
        
        type Node = usize;

        fn new_leaf(&mut self, label: String) -> Self::Node {
            let node_id = self.node_id;
            self.node_id += 1;
            println!("Leaf {}: label = {}", node_id, label);
            node_id
        }

        fn new_node(&mut self, children: Vec<Self::Node>) -> Self::Node {
            let node_id = self.node_id;
            self.node_id += 1;
            println!("Internal node {}: children = {:?}", node_id, children);
            node_id
        }

        fn set_root(&mut self, root: Self::Node) {
            println!("Root = node {}", root);
        }
    }

    #[test]
    fn first_test() {
        let mut tree = String::new();
        {
            let f = File::open("../test_data/test_trees/947-processed-no-tree-names.txt").unwrap();
            let mut reader = BufReader::new(f);
            reader.read_line(&mut tree).unwrap();
        }
        let mut bld = TestBuilder { node_id: 0 };
        let mut parser = Parser::new(&mut bld);
        parser.parse_tree(&tree);
        print!("{}", tree);
    }
}
