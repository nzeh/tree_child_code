//! This module encapsulates all the wrapper code to bundle the tree-child sequence code into a
//! complete binary.

mod config;
mod io;
mod logic;
mod result;

pub use self::config::Config;
pub use self::io::{read_input, write_output};
pub use self::logic::{TcResult, tree_child_sequence_or_network};
pub use self::result::{Result, Error};
