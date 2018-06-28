#[macro_use]
extern crate clap;
extern crate tree_child;

use std::fmt;
use std::fmt::Write;
use std::fs;
use std::io;
use std::io::Read;

use tree_child::clusters;
use tree_child::newick;
use tree_child::tree::{Tree, TreeBuilder};
use tree_child::tree_child_sequence::{tree_child_sequence, TcSeq, Pair};

/// A wrapper to catch both I/O and parse errors from the Newick parser
enum AppError {
    ParseError(newick::Error),
    IOError(io::Error),
}

impl From<io::Error> for AppError {

    fn from(e: io::Error) -> Self {
        AppError::IOError(e)
    }
}

impl From<newick::Error> for AppError {

    fn from(e: newick::Error) -> Self {
        AppError::ParseError(e)
    }
}

impl fmt::Display for AppError {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (err_type, msg): (&str, &fmt::Display) = match self {
            AppError::IOError(e)    => ("I/O error",   e),
            AppError::ParseError(e) => ("Parse error", e),
        };
        write!(f, "{}: {}", err_type, msg)
    }
}

/// A result type whose error type is Error
type Result<T> = std::result::Result<T, AppError>;

/// Main function
fn main() {
    let args = clap_app!(
        TcSeq =>
        (version: env!("CARGO_PKG_VERSION"))
        (author: "Norbert Zeh <nzeh@cs.dal.ca>")
        (about: "Compute a tree-child sequence of a set of binary phylogenetic trees")
        (@arg output: -o --output [output] "the file to write the resulting sequence to (stdout if absent)")
        (@arg input: <input> "The file containing the set of input trees")
        (@arg dont_use_clustering: -c --("no-clustering") "Disable the use of cluster reduction to speed up the code")
        //(@arg dont_limit_fanout: -b --("no-branch-bound") "Disable limiting the branching fan-out based on the hybridization number")
    ).get_matches();

    let input          = args.value_of("input").unwrap();
    let output         = args.value_of("output");
    let use_clustering = !args.is_present("dont_use_clustering");
    //let limit_fanout   = !args.is_present("dont_limit_fanout");

    let trees = match read_input(input) {
        Ok(trees) => trees,
        Err(e)    => {
            eprintln!("{}", e);
            std::process::exit(1);
        },
    };

    let tc_seq = if use_clustering {
        let clusters = clusters::partition(trees);
        let seqs = clusters.into_iter().map(|trees| tree_child_sequence(trees)).collect();
        clusters::combine_tc_seqs(seqs)
    } else {
        tree_child_sequence(trees)
    };

    if let Err(e) = write_output(output, tc_seq) {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

/// Read the input from a file
fn read_input(file_name: &str) -> Result<Vec<Tree<String>>> {
    let mut newick = String::from("");
    fs::File::open(file_name)?.read_to_string(&mut newick)?;
    let mut builder: TreeBuilder<String> = TreeBuilder::new();
    newick::parse_forest(&mut builder, &newick)?;
    Ok(builder.trees())
}

/// Write the result to a file or stdout
fn write_output(file_name: Option<&str>, tc_seq: TcSeq<String>) -> io::Result<()> {
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
