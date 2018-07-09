//! This module contains all the code for reading the input of `tc_seq` and writing the result of
//! the computation back to screen or to a file.

use std::fmt::Write;
use std::fs;
use std::io;
use std::io::Read;
use app;
use network::TcNet;
use newick;
use tree::{Tree, TreeBuilder};
use tree_child_sequence::TcSeq;

/// Read the input from a file
pub fn read_input(file_name: &str) -> app::Result<Vec<Tree<String>>> {
    let mut newick  = String::from("");
    let mut builder = TreeBuilder::new();
    fs::File::open(file_name)?.read_to_string(&mut newick)?;
    newick::parse_forest(&mut builder, &newick)?;
    Ok(builder.trees())
}

/// Write the result to a file or stdout
pub fn write_output(file_name: Option<&str>, tc_result: app::TcResult) -> app::Result<()> {
    let mut file: Box<io::Write> = match file_name {
        Some(file_name) => Box::new(fs::File::create(file_name)?),
        None            => Box::new(io::stdout()),
    };
    let output = format_output(tc_result);
    write!(file, "{}", output)?;
    Ok(())
}

/// Format the tree-child sequence or network
fn format_output(tc_result: app::TcResult) -> String {
    match tc_result {
        app::TcResult::Net(net) => format_tc_net(net),
        app::TcResult::Seq(seq) => format_tc_seq(seq),
    }
}

/// Format a tree-child sequence
fn format_tc_seq(tc_seq: TcSeq<String>) -> String {
    let mut output = String::new();
    for pair in tc_seq {
        writeln!(&mut output, "{}", pair).unwrap();
    }
    output
}

/// Format a tree-child network
fn format_tc_net(tc_net: TcNet<String>) -> String {
    format!("{}\n", newick::format_network(&tc_net).unwrap())
}
