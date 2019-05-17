//! This module contains all the command line parsing code and provides a `Config` struct that
//! encapsulates all the parsed configuration options.

use clap::{App, Arg};
use num_cpus;

/// A structure to hold all the configuration parameters
pub struct Config {
    /// The name of the input file
    pub input: String,

    /// The name of the output file
    pub output: Option<String>,

    /// Enable the use of cluster reduction
    pub use_clustering: bool,

    /// Enable redundant branch optimization
    pub use_redundant_branch_opt: bool,

    /// Limit the fanout based on the current weight bound
    pub limit_fanout: bool,

    /// The number of worker threads to use
    pub num_threads: usize,

    /// The number of branches each thread should explore between polls for idle threads
    pub poll_delay: Option<usize>,

    /// Compute a tree-child network instead of a tree-child sequence as output
    pub compute_network: bool,

    /// Look for a binary tree-child sequence or network (every reticulation node has exactly two
    /// parents)
    pub binary: bool,
}

impl Config {
    /// Create a new config object from the command line arguments
    pub fn new() -> Self {
        // Define the acceptable arguments
        let args = [
            Arg::with_name("input")
                .required(true)
                .takes_value(true)
                .value_name("input")
                .help("input file")
                .long_help(
"input file; contains the set of trees in Newick format, one tree per line"),
            Arg::with_name("output")
                .required(false)
                .takes_value(true)
                .value_name("output")
                .short("o")
                .long("output")
                .help("output file")
                .long_help(
"output file; receives the computed tree-child sequence"),
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
"Number of branches to explore between checks for idle threads to share work with; \
\"infinite\" = disable checks. If this option is absent, this is equivalent to \
\"-w infinite\" if the number of threads is one and to \"-w 1\" if the number \
of threads is greater than one."),
            Arg::with_name("compute_sequence")
                .short("s")
                .long("--compute-sequence")
                .required(false)
                .takes_value(false)
                .help("output a tree-child sequence")
                .long_help("output a tree-child sequence"),
            Arg::with_name("compute_network")
                .conflicts_with("compute_sequence")
                .short("n")
                .long("--compute-network")
                .required(false)
                .takes_value(false)
                .help("output a tree-child network")
                .long_help("output a tree-child network in extended Newick format"),
            Arg::with_name("binary")
                .short("b")
                .long("binary")
                .required(false)
                .takes_value(false)
                .help("find a binary tree-child sequence or network")
                .long_help("find a binary tree-child sequence or network"),
        ];

        // Parse the arguments
        let args = App::new(crate_name!())
            .version(crate_version!())
            .author(crate_authors!())
            .about("Compute a tree-child sequence of a set of binary phylogenetic trees")
            .long_about("Compute a tree-child sequence of a set of binary phylogenetic trees")
            .args(&args)
            .get_matches();

        let input = args.value_of("input").unwrap().to_string();
        let output = args.value_of("output").map(|s| s.to_string());
        let use_clustering = !args.is_present("dont_use_clustering");
        let use_redundant_branch_opt = args.is_present("optimize_redundant_branches");
        let limit_fanout = !args.is_present("dont_limit_fanout");
        let num_threads = num_threads(args.value_of("num_threads"));
        let poll_delay = poll_delay(args.value_of("poll_delay"), num_threads);
        let compute_network = !args.is_present("compute_sequence");
        let binary = args.is_present("binary");

        Self {
            input,
            output,
            use_clustering,
            use_redundant_branch_opt,
            limit_fanout,
            num_threads,
            poll_delay,
            compute_network,
            binary,
        }
    }
}

/// Check that the provided number of threads is valid
fn validate_num_threads(arg: String) -> Result<(), String> {
    match arg.parse::<usize>() {
        Ok(x) if x > 0 => Ok(()),
        Err(_) if arg.to_lowercase() == "native" => Ok(()),
        _ => Err(String::from(
            "Number of threads must be \"native\" or a positive integer",
        )),
    }
}

/// Query the number of threads to use
fn num_threads(arg: Option<&str>) -> usize {
    match arg.map(|arg| arg.parse::<usize>()) {
        Some(Ok(n)) => n,
        Some(_) => num_cpus::get(),
        None => 1,
    }
}

/// Check that the poll delay is valid
fn validate_poll_delay(arg: String) -> Result<(), String> {
    match arg.parse::<usize>() {
        Ok(x) if x > 0 => Ok(()),
        Err(_) if arg.to_lowercase() == "infinite" => Ok(()),
        _ => Err(String::from(
            "Poll delay must be \"infinite\" or a positive integer",
        )),
    }
}

/// Query the poll delay to use
fn poll_delay(arg: Option<&str>, num_threads: usize) -> Option<usize> {
    match arg.map(|arg| arg.parse::<usize>()) {
        Some(Ok(n)) => Some(n),
        Some(_) => None,
        None if num_threads == 1 => None,
        _ => Some(1),
    }
}
