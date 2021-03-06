//! This module provides result and error types for the main binary `tc_seq`.

use tree_child::newick;
use std::fmt;
use std::io;
use std::result;

/// A result type for functions in the tc_seq app
pub type Result<T> = result::Result<T, Error>;

/// A wrapper to catch both I/O and parse errors from the Newick parser
pub enum Error {
    /// Error from the Newick parser
    ParseError(newick::Error),

    /// I/O error
    IOError(io::Error),

    /// Failure to find a sequence or network (can happen if we're looking for binary networks)
    Fail,
}

/// AppError can be created from an I/O error
impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::IOError(e)
    }
}

/// AppError can be created from a Newick error
impl From<newick::Error> for Error {
    fn from(e: newick::Error) -> Self {
        Error::ParseError(e)
    }
}

/// Displaying an AppError shows what type of error it wraps and the message of the wrapped error
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (err_type, msg): (&str, &dyn fmt::Display) = match self {
            Error::IOError(e) => ("I/O error", e),
            Error::ParseError(e) => ("Parse error", e),
            Error::Fail => ("Error", &"This set of input trees has no binary tree-child network"),
        };
        write!(f, "{}: {}", err_type, msg)
    }
}
