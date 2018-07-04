#[macro_use]
extern crate clap;
extern crate num_cpus;
extern crate tree_child;

use clap::{App, Arg};

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

    /// Error from the Newick parser
    ParseError(newick::Error),

    /// I/O error
    IOError(io::Error),
}

/// AppError can be created from an I/O error
impl From<io::Error> for AppError {

    fn from(e: io::Error) -> Self {
        AppError::IOError(e)
    }
}

/// AppError can be created from a Newick error
impl From<newick::Error> for AppError {

    fn from(e: newick::Error) -> Self {
        AppError::ParseError(e)
    }
}

/// Displaying an AppError shows what type of error it wraps and the message of the wrapped error
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
                Err(String::from(
                        "Number of threads must be \"native\" or a positive integer"))
            },
            Err(_) => Err(String::from(
                    "Number of threads must be \"native\" or a positive integer")),
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
                Err(String::from(
                        "Poll delay must be \"infinite\" or a positive integer"))
            },
            Err(_) => Err(String::from(
                    "Poll delay must be \"infinite\" or a positive integer")),
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

    // Define the acceptable arguments
    let args = [
        Arg::with_name("input")
            .required(true)
            .takes_value(true)
            .value_name("input")
            .help("input file")
            .long_help("input file; contains the set of trees in Newick format, one tree per line"),
        Arg::with_name("output")
            .required(false)
            .takes_value(true)
            .value_name("output")
            .short("o")
            .long("output")
            .help("output file")
            .long_help("output file; receives the computed tree-child sequence"),
        Arg::with_name("dont_use_clustering")
            .required(false)
            .takes_value(false)
            .short("c")
            .long("no-clustering")
            .help("disable clustering")
            .long_help("disable clustering"),
        Arg::with_name("optimize_redundant_branches")
            .required(false)
            .takes_value(false)
            .short("r")
            .long("redundant-branch-opt")
            .help("enable redundant branch elimination")
            .long_help(
"do not explore branches that resolve the same cherries already resolved in sibling branches \
(EXPERIMENTAL)"),
        Arg::with_name("dont_limit_fanout")
            .required(false)
            .takes_value(false)
            .short("b")
            .long("no-branch-bound")
            .help("disable FPT limiting of branch fanout")
            .long_help(
"disable limiting of branch fanout based on the current hybridization number"),
        Arg::with_name("num_threads")
            .short("p")
            .long("num-threads")
            .required(false)
            .takes_value(true)
            .value_name("n")
            .validator(validate_num_threads)
            .help("the number of threads to use")
            .long_help(
"the number of threads to use; \"native\" = one thread per logical core. \
If this option is absent, this is equivalent to \"-p 1\" (single-threaded execution)."),
        Arg::with_name("poll_delay")
            .short("w")
            .long("poll-delay")
            .required(false)
            .takes_value(true)
            .value_name("n")
            .validator(validate_poll_delay)
            .help("number of branches to explore between idle checks")
            .long_help(
"Number of branches to explore between checks for idle threads to share work with;\
\"infinite\" = disable checks. If this option is absent, this is equivalent to \
\"-w infinite\" if the number of threads is one and to \"-w 1\" if the number \
of threads is greater than one.")
    ];

    // Parse the arguments
    let args = App::new(crate_name!())
        .version(crate_version!())
        .author(crate_authors!())
        .about("Compute a tree-child sequence of a set of binary phylogenetic trees")
        .long_about("Compute a tree-child sequence of a set of binary phylogenetic trees")
        .args(&args)
        .get_matches();

    // Extract configuration options
    let input                    = args.value_of("input").unwrap();
    let output                   = args.value_of("output");
    let use_clustering           = !args.is_present("dont_use_clustering");
    let use_redundant_branch_opt = args.is_present("optimize_redundant_branches");
    let limit_fanout             = !args.is_present("dont_limit_fanout");
    let num_threads              = num_threads(args.value_of("num_threads"));
    let poll_delay               = poll_delay(args.value_of("poll_delay"), num_threads);

    // Read the input trees
    let trees = match read_input(input) {
        Ok(trees) => trees,
        Err(e)    => {
            eprintln!("{}", e);
            std::process::exit(1);
        },
    };

    // Compute the tree-child sequence
    let tc_seq = if use_clustering {
        // ... with clustering
        let clusters = clusters::partition(trees);
        let seqs = clusters.into_iter().map(
            |trees| tree_child_sequence(
                trees, num_threads, poll_delay, limit_fanout, use_redundant_branch_opt)).collect();
        clusters::combine_tc_seqs(seqs)
    } else {
        // ... or without
        tree_child_sequence(trees, num_threads, poll_delay, limit_fanout, use_redundant_branch_opt)
    };

    // Write the result to stdout or the output file if provided
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
