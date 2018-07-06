//! This crate implements code for computing a tree-child sequence of a collection of trees.

#[macro_use]
extern crate clap;
extern crate num_cpus;

pub mod app;
pub mod clusters;
pub mod newick;
pub mod tree;
pub mod tree_child_sequence;
