#[macro_use]
extern crate clap;
extern crate num_cpus;
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

/// Check that the provided number of threads is valid
fn validate_num_threads(arg: String) -> std::result::Result<(), String> {
    if arg.to_lowercase() == "native" {
        Ok(())
    } else {
        match arg.parse::<usize>() {
            Ok(x) => if x > 0 {
                Ok(())
            } else {
                Err(String::from("Number of threads must be \"native\" or a positive integer"))
            },
            Err(_) => Err(String::from("Number of threads must be \"native\" or a positive integer")),
        }
    }
}

/// Query the number of threads to use
fn num_threads(arg: Option<&str>) -> usize {
    if let Some(arg) = arg {
        if arg.to_lowercase() == "native" {
            num_cpus::get()
        } else {
            arg.parse::<usize>().unwrap()
        }
    } else {
        1
    }
}

/// Check that the poll delay is valid
fn validate_poll_delay(arg: String) -> std::result::Result<(), String> {
    if arg.to_lowercase() == "infinite" {
        Ok(())
    } else {
        match arg.parse::<usize>() {
            Ok(x) => if x > 0 {
                Ok(())
            } else {
                Err(String::from("Poll delay must be \"infinite\" or a positive integer"))
            },
            Err(_) => Err(String::from("Poll delay must be \"infinite\" or a positive integer")),
        }
    }
}

/// Query the poll delay to use
fn poll_delay(arg: Option<&str>, num_threads: usize) -> Option<usize> {
    if let Some(arg) = arg {
        if arg.to_lowercase() == "infinite" {
            None
        } else {
            Some(arg.parse::<usize>().unwrap())
        }
    } else {
        if num_threads == 1 {
            None
        } else {
            Some(1)
        }
    }
}

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
        (@arg optimize_redundant_branches: -r --("redundant-branch-opt") "Enable the elimination of redundant branches in the search
(EXPERIMENTAL)")
        (@arg dont_limit_fanout: -b --("no-branch-bound") "Disable limiting the branching fan-out based on the
hybridization number")
        (@arg num_threads: -p --("num-threads") [n] {validate_num_threads} "the number of threads to use or \"native\" for the number
of logical cores
If this option is absent, the code runs using a single thread")
        (@arg poll_delay: -w --("poll-delay") [n] {validate_poll_delay} "the number of branches each thread should explore between
checks for idle threads or \"infinite\" to disable checking
If this option is absent, this is equivalent to \"-w infinite\" if
running single-threaded and to \"-w 1\" if running multi-threaded")
    ).get_matches();

    let input                    = args.value_of("input").unwrap();
    let output                   = args.value_of("output");
    let use_clustering           = !args.is_present("dont_use_clustering");
    let use_redundant_branch_opt = args.is_present("optimize_redundant_branches");
    let limit_fanout             = !args.is_present("dont_limit_fanout");
    let num_threads              = num_threads(args.value_of("num_threads"));
    let poll_delay               = poll_delay(args.value_of("poll_delay"), num_threads);

    let trees = match read_input(input) {
        Ok(trees) => trees,
        Err(e)    => {
            eprintln!("{}", e);
            std::process::exit(1);
        },
    };

    let tc_seq = if use_clustering {
        let clusters = clusters::partition(trees);
        let seqs = clusters.into_iter().map(
            |trees| tree_child_sequence(trees, num_threads, poll_delay, limit_fanout, use_redundant_branch_opt)).collect();
        clusters::combine_tc_seqs(seqs)
    } else {
        tree_child_sequence(trees, num_threads, poll_delay, limit_fanout, use_redundant_branch_opt)
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
