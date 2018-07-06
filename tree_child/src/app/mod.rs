//! This module encapsulates all the wrapper code to bundle the tree-child sequence code into a
//! complete binary.

mod config;
mod io;
mod logic;
mod result;

pub use self::config::Config;
pub use self::io::{read_input, write_output};
pub use self::logic::tree_child_sequence;
pub use self::result::{Result, Error};
