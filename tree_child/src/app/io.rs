//! This module contains all the code for reading the input of `tc_seq` and writing the result of
//! the computation back to screen or to a file.

use std::fmt::Write;
use std::fs;
use std::io;
use std::io::Read;
use app;
use newick;
use tree::{Tree, TreeBuilder};
use tree_child_sequence::{Pair, TcSeq};

/// Read the input from a file
pub fn read_input(file_name: &str) -> app::Result<Vec<Tree<String>>> {
    let mut newick = String::from("");
    fs::File::open(file_name)?.read_to_string(&mut newick)?;
    let mut builder: TreeBuilder<String> = TreeBuilder::new();
    newick::parse_forest(&mut builder, &newick)?;
    Ok(builder.trees())
}

/// Write the result to a file or stdout
pub fn write_output(file_name: Option<&str>, tc_seq: TcSeq<String>) -> app::Result<()> {
    let mut file: Box<io::Write> = match file_name {
        Some(file_name) => Box::new(fs::File::create(file_name)?),
        None            => Box::new(io::stdout()),
    };
    let output = format_output(tc_seq);
    write!(file, "{}", output)?;
    Ok(())
}

/// Format the tree-child sequence
fn format_output(tc_seq: TcSeq<String>) -> String {
    let mut output = String::new();
    for pair in tc_seq {
        match pair {
            Pair::Reduce(u, v) => writeln!(&mut output, "({}, {})", u, v),
            Pair::Final(u)     => writeln!(&mut output, "({}, -)", u),
        }.unwrap();
    }
    output
}
