# Description

This is an implementation of our algorithm for finding a tree-child sequence for a collection of binary phylogenetic trees.  Its implementation is split into multiple modules and submodules described below.

The implementation supports multifurcating trees where this was possible without any new algorithmic insights (the tree representation itself, parsing Newick strings, cluster partitioning), but the algorithm as a whole works only for binary trees at the moment because the search for a tree-child sequence itself does not currently support multifurcating trees.  This is not just an implementation issue but an algorithmic one.

# Modules

## main

This is where the main code lives.  It takes care of command-line handling and little else.

## tree

This module provides the `Tree` and `TreeBuilder` types and methods on them.  `Tree` is the basic representation of a phylogenetic tree.  It supports primitive operations for querying the structure of the tree and manipulating it by cutting off leaves and suppressing degree-2 nodes.

Every leaf in the tree stores a "pointer" to its parent and a label.  Every internal node stores "pointers" to its parent and to its children.  I opted for a representation where every node explicitly stores an array of pointers to its children instead of one where every node points to its leftmost child and children are linked to form a doubly-linked list.  The latter would allow most manipulations of the tree in constant time while the former makes deletion of a child take time proportional to the degree of the node in the worst case.  However, the overhead of the linked-list implementation, both in complexity and consequently also in running time, seemed substantial.  Given that (a) we currently only support binary trees and (b) I don't expect many very high-degree nodes even in multifurcating trees, the simpler implementation chosen here is likely to be faster most of the time and is certainly simpler.

Since Rust's ownership model makes circular pointer structures impossible, I chose to simulate them by representing every `Tree` as an array of nodes, which allows the simulation of pointers without the ownership headaches using array indices.  This has two added benefits: (1) Many fewer allocations and contiguous storage of the tree structure.  This may help cache efficiency.  (2) Packaging a tree to send it to a different thread when we parallelize the code becomes trivial because all that is required is to clone the vector.

Trees refer to their nodes using two types of identifiers.  The `Leaf` type is an identifier for a leaf.  The corresponding `Node` identifier can be looked up using the `leaf` method.  The `Node` type is an identifier for a node.  Both are glorified indices into leaf and node arrays.  The need for two different types arises because `Node`s are unique to a given tree while `Leaf`s are global identifiers shared by a collection of trees.  Specifically, the `TreeBuilder` discussed below ensures that two leaves with the same label and in different trees have the same `Leaf` identifier, which allows easy cross referencing between leaves both during the construction of clusters and during the search for a tree-child sequence. 

The `TreeBuilder` is the type we use to construct a collection of trees, both in the implementation of the Newick parser and in computing a cluster partition of a set of trees.  The `TreeBuilder` ensures the above properties that `Leaf` identifiers are consistent between trees constructed using the same `TreeBuilder`.

## newick

This module provides four simple functions for parsing a Newick string into an internal `Tree` representation.  `parse_tree` expects a one-line Newick string and parses it into a tree.  `parse_forest` expects a multi-line Newick string and parses it into a vector of trees.  Thanks to its use of a `TreeBuilder`, `parse_forest` ensures that leaves with the same label have the same `Leaf` identifier across all trees.  `format_tree` and `format_forest` turn the tree/forest back into a Newick string.

One caveat is that the parser supports labels of internal nodes and edge lengths in the Newick string, in order to be as general as possible.  The formatting functions output internal nodes without labels and do not write any edge lengths.  This is because the algorithm has no notion of labelled internal nodes and edge lengths, so the parser discards them and the formatter cannot reproduce them.

## clusters

This module implements a simple linear-time cluster partitioning algorithm.  It fails to find soft clusters that would be present in appropriate binary resolutions of the input trees but are not represented as nodes of the multifurcating input trees.  Such soft clusters can be found in linear time but using a much more complicated algorithm.  At this point, this simple algorithm is sufficient because (a) we support only binary trees for now and (b) I expect that we won't miss all that many clusters even on multifurcating inputs.

Given a vector of `Tree`s, the `partition` function produces a vector of vectors of `Tree`s.  Each vector of `Tree`s represents a cluster.  In order to facilitate reconstruction of a tree-child sequence (and later network) from tree-child sequences of the clusters, the leaves of the trees in each cluster are labelled with an `LoC` type (leaf or cluster) to mark whether a cluster leaf is an original input leaf or a leaf representing a child cluster. 

## tree_child_sequence

This is the main module representing the recursive search algorithm for a tree-child sequence.  It is split into multiple submodules to keep my sanity.  A tree-child sequence is computed using `tree_child_sequence`.  All this function does is construct a `Search` object and invokes its `run` method.  `run` iteratively increases the parameter and launches the recursive search using the given parameter until the search succeeds.

A `Search` object has a `State`, implemented in the `state` submodule and a `History`, implemented in the `history` submodule.  The `State` keeps track of the current set of trees and the set of cherries in these trees.  The `History` is used to record all operations performed on the `State` so they can be undone as the recursive search backtracks.  This avoids copying of the entire search state every time a recursive call is made.  Instead, the search state is modified in place and then rolled back to its state before the recursive call, representing by a history `Snapshot`, when the recursive call returns.  This should be faster.

The `State` supports numerous methods for manipulating the list of cherries, including classifying them as trivial or non-trivial, for pruning and restoring leaves in the collection of trees, and for manipulating the current tree-child sequence.  It uses two additional types in its implementation.  A `search::leaf::Leaf` (implemented in the `leaf` submodule) represents information about a leaf (the number of trees it belongs to and the list of cherries it participates in).  A `search::cherry::Cherry` (implemented in the `cherry` submodule) represents information about a cherry (the leaves that are part of this cherry and the list of trees that have this cherry).