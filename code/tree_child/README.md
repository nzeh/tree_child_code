# Computing Optimal Tree-Child Networks from Sets of Binary Phylogenetic Trees

This is an implementation of the algorithm for computing optimal tree-child networks from sets of binary phylogenetic trees published in

>  **A Practical Fixed-Parameter Algorithm for Constructing Tree-Child Networks from Multiple Binary Trees**  
> *Leo van Iersel, Remie Janssen, Mark Jones, Yukihiro Murakami, and Norbert Zeh*

For a detailed description of the algorithm, see the paper.  This README only discusses how to compile and run the code, and the code organization in the hope that this is useful for anyone who wants to work with or modify the code.

## How to Compile

To compile the code, you need a working Rust compiler (tested with version 1.29 and higher) and *cargo*.  For installation instructions, see [https://www.rust-lang.org/learn/get-started]().  Once Rust and cargo are installed, run

```shell
$ cargo build --release
```

to build the code.  The compiled executable can be found in `target/release/tc_seq`.  (If you want the debug version, use `cargo build —debug` or `cargo build`.  The compiled binary is found in `target/debug/tc_seq` in this case.)

## How to Run

The compiled code can be run either by invoking one of the compiled binaries above or by running

```shell
$ cargo run [--debug|--release]
```

This prints information about command-line arguments and then exits.  The following command-line arguments are accepted:

### Required

- `<input>`: The name of the input file that contains the set of input trees in Newick format, one tree per line.

### Optional: Controlling the Output

- `-s`: Output a tree-child sequence.  This is the default.
- `-n`: Output a tree-child network in Newick format.
- `-B`: Look for binary tree-child sequences/networks.  A binary tree-child network is one where every reticulation has exactly two parents.  This may fail to find a network because there exist sets of trees that are not displayed by any binary tree-child network.  A binary tree-child sequence is one corresponding to a binary tree-child network.  This simply means that every leaf occurs as the first element of at most two pairs in the sequence.
- `-o <output>`: The file to which the computed output is to be written.  Without this option, output is sent to `stdout`.

### Optional: Controlling the Behaviour of the Algorithm

These options exist mainly to evaluate the effect of different optimizations and parameters on the algorithm's running time.  Only the `-p` option should normally be used in "production use".

- `-b`: By default, the algorithm aborts a branch when there are more than 4*k* cherries because, as shown in the paper, this means that any tree-child network displaying the set of input trees must have more than *k* reticulations.  This flag disables this behaviour, that is, a branch is never aborted even if there are way too many cherries.  This option exists to investigate whether this bounding of the fan-out of the search has any significant impact on the algorithm's running time in practice.
- `-c`: Do not use cluster reduction.  Again, this option exists to investigate the impact of cluster reduction on the algorithm's running time.
- `-r`: Do not use redundant branch elimination.  Again, this option exists to investigate the impact of cluster reduction on the algorithm's running time.
- `-p`: Specify the number of parallel threads to use.  The default is `-pnative`, which runs twice as many threads as there are cores.  `-p1` forces single-threaded execution.  `-p<n>` runs *n* threads.
- `-w`: The work-sharing load balancing strategy requires that busy threads check for work requests from idle threads (see discussion below).  In theory, too frequent checks lead to a slow-down because threads spend too much time checking for messages relative to the amount of work they perform on the actual search; too infrequent checks result in idle threads waiting for work for too long, which also hurts performance.  `-w<n>` means that each busy thread checks for messages every *n* iterations through its main loop, where one iteration corresponds to one recursive call in a recursive formulation of the algorithm.  In practice, any reasonably small value of *n* is fine.  The default is `-w100`.

## Code Organization

The code is split into two main components. `lib.rs` and its submodules provides an implementation of the algorithm.  This does not compile to a standalone binary but is meant to be included in an application program that wants to use the algorithm to compute tree-child networks.  The second main component is a fairly thin wrapper that adds the boilerplate code to obtain an executable that can read a Newick-formatted set of input trees and outputs an optimal tree-child sequence or an optimal tree-child network for this set of trees.

The following is a list of the most important modules and the functionalities they provide:

### bin/

This directory contains all the wrapper code to obtain a binary that can be run on Newick-formatted sets of input trees.  The top-level source file is `tc_seq.rs`.  This file imports the library code implementing the algorithm for computing tree-child networks as well as the following sets of modules that are part of the wrapper code:

- `app::config` implements command line parsing.
- `app::io` provides functions to read the input and write the results.
- `app::logic` provides wrapper functions for calling the tree-child sequence code and returning either the computed sequence or a network corresponding to the computed sequence.
- `app::result` provides a `Result` type used throughout the application.

### tree.rs

This module provides the `Tree` and `TreeBuilder` types and methods on them.  `Tree` is the basic representation of a phylogenetic tree.  It supports primitive operations for querying the structure of the tree and manipulating it by cutting off leaves and suppressing degree-2 nodes.

Trees refer to their nodes using two types of identifiers.  The `Leaf` type is an identifier for a leaf.  The corresponding `Node` identifier can be looked up using the `leaf` method.  The `Node` type is an identifier for a node.  Both are glorified indices into leaf and node arrays.  The need for two different types arises because `Node`s are unique to a given tree while `Leaf`s are global identifiers shared by a collection of trees.  Specifically, the `TreeBuilder` discussed below ensures that two leaves with the same label and in different trees have the same `Leaf` identifier, which allows easy cross referencing between leaves both during the construction of clusters and during the search for a tree-child sequence. 

The `TreeBuilder` is the type used to construct a collection of trees, both in the implementation of the Newick parser and in computing a cluster partition of a set of trees.  The `TreeBuilder` ensures the above properties that `Leaf` identifiers are consistent between trees constructed using the same `TreeBuilder`.

### network.rs

This module provides a structure `TcNet`, which is used to represent tree-child networks.  The main use of this structure is to construct it from a tree-child sequence using `TcNet::from_seq` and then pass it to `newick::format_network` to output a Newick string representing the network.  Beyond this, the code does not use this structure.

### newick.rs

This module provides five simple functions for parsing a Newick string into an internal `Tree` representation and for generating output in Newick format.  `parse_tree` expects a one-line Newick string and parses it into a tree.  `parse_forest` expects a multi-line Newick string and parses it into a vector of trees.  Thanks to its use of a `TreeBuilder`, `parse_forest` ensures that leaves with the same label have the same `Leaf` identifier across all trees.  `format_tree`, `format_forest`, and `format_network` turn the tree/forest/network back into a Newick string.

Networks are represented using extended Newick format as, for example, understood by *Dendroscope*.  The network is represented as a tree.  Reticulation nodes are internal nodes with labels of the form *#H\<n>*.  Additional parent edges of reticulation nodes are then generated by having leaves with the same label *#H\<n>*, which are considered to be the same node as the reticulation node.

To be able to handle as general inputs as possible, the parser supports labels on internal nodes and edge lengths as part of the Newick strings.  Since this information is meaningless in the context of the tree-child network construction algorithm, these labels and edge lengths are discarded in the output.  (In fact, they are already discarded in the internal tree representation, that is, the parser recognizes labels of internal nodes and edge lengths but silently ignores them.)

### clusters.rs

This module implements a simple linear-time cluster partitioning algorithm for binary trees.  Given a vector of `Tree`s, the `partition` function produces a vector of vectors of `Tree`s.  Each vector of `Tree`s represents a cluster.  In order to facilitate reconstruction of a tree-child sequence (and later network) from tree-child sequences of the clusters, the leaves of the trees in each cluster are labelled with an `LoC` type (leaf or cluster) to mark whether a cluster leaf is an original input leaf or a leaf representing a child cluster. 

The other function exported by this module is `combine_tc_seqs`, which takes a vector of tree-child sequences for a set of clusters and combines these sequences into a tree-child sequence for the trees that were partitioned into these clusters.

### tree_child_sequence/

This is the main module representing the recursive search algorithm for a tree-child sequence.  Its main export is a data type `TcSeq` for representing tree-child sequences and a function `tree_child_sequence` that computes a `TcSeq` from a vector of input trees.  Its implementation is split into a number of submodules.

#### Parallel Implementation Modules

The code is parallelized using a work-sharing scheduler.  A *master thread*, implemented in `tree_child_sequence::master::Master`, controls the search for a solution.  Its `run` method runs a number of iterations, increasing the target number of iterations *k* in each iteration, until either a tree-child network with the given number of reticulations is found or the algorithm concludes that no solution exists (which is possible when looking for binary tree-chlid networks, ones where every reticulation has exactly two parents).

The master thread sends a `Search` object representing the initial state of the recursive search for a tree-child sequence of weight at most *k* to one of a number of *worker threads*.  The worker threads are implemented in `tree_child_sequence::worker::Worker`.  A new worker is spawned using `Worker::spawn`.  The worker then runs forever until it receives a `Message` instructing it to quit.  As long as the worker runs, it either works on its part of a search for a tree-child sequence of weight at most *k* or it is idle.  In the latter case, it sends a message to each of the other workers, asking it for part of its workload.  The targeted worker either replies that it is idle itself or sends part of its work.  This exchange of data is implemented in `Worker::get_work`.

When a worker finds a tree-chlid sequence of weight at most *k*, it sends it to the master, which then sends a message to all workers to instruct them to quit and returns the result.  If all workers finish their search unsuccessfully, then the last worker to go idle sends a failure message to the master.  In response, the master starts the next iteration of the main loop, increasing *k* by one.

The communication between the different threads is handled by a channel implemented in `tree_child_sequence::channel`.  The main method to create a channel is `channel`.  It returns a `Sender` object and a `Receiver` object representing the two ends of the channel.  This is analogous to standard channels created using `std::mpsc::channel`.  However, these standard channels use mutexes and condition variables in their implementation, which could be fairly costly for very frequent and fine-grained communication.  Because of this, this code uses its own channel implementation based on spinlocks.

#### Implementation of the Recursive Search

The state of the search is represented by a `Search` object implemented in `tree_child_sequence::search`.  This object stores the current set of trees, the current partial tree-child sequence, and information about the cherries in the trees.  It provides numerous methods to manipulate this state.

Three aspects of the implementation of `Search` are noteworthy:

1. The search state is a fairly fat object, so copying it is costly.  However, a naïve implementation of the recursive search requires that each recursive call has its own copy of the search state it operates on.  To avoid the resulting copying cost, all recursive calls made by the same worker thread share one representation of its state.  This state is stored in a `tree_child_sequence::search::state::State` object.  The `Search` object of the thread packages this `State` with a `History` that records the changes made to the `State`.  Whenever a recursive call is made, the algorithm "takes a snapshot", that is, records the current length of the `History`.  When the recursive call returns, it undoes all the operations on the `History` since this snapshot, thereby restoring the `State` to the state it was in before the recursive call was made.
2. Whenever a worker thread receives a work request from another thread, it needs to share part of its workload with that thread.  This is done by marking some branch of the recursive search as sent to another thread and sending a copy of the current thread's search state corresponding to this branch to the requesting worker.  The thread that sends this branch to the requesting worker then skips this sent branch in its own search.  To avoid frequently sending very small parts of a thread's search tree to other threads, the thread always sends a largest branch of its own search to the requesting thread.  To enable this, each thread implements its recursion not by making recursive calls but by explicitly maintaining its own recursion stack.  The branch sent in response to a work request is then taken from the *bottom* of the recursion stack instead of the top.
3. The redundant branch elimination heuristic is described as maintaining a set of pairs that are redundant for the current partial tree-child sequence.  Whenever the algorithm tries to branch on a pair `(x,y)`, checking whether this pair is currently in the set of redundant pairs is potentially costly.  The implementation detects redundant pairs differently, which is easily seen to be equivalent to the description given in the paper.  For each cherry, `{x,y}`, the algorithm maintains two counts, and `x`-count and a `y`-count, equal to the number of trees that contained the cherry `{x,y}` the last time an ancestor invocation of the current recursive call branched on the pair `(x,y)` or `(y,x)`, respectively.  Whenever a pair `(x,y)` is added to the tree-child sequence, the `z`-count is reset to 0 for every cherry `{x,z}` of the current set of trees.  It is easily checked that the pair `(x,y)` is redundant for the current partial tree-child sequence if and only if the current `x`-count stored with the cherry `{x,y}` equals the number of trees in the current set of trees that have `{x,y}` as a cherry.

The `tree_child_sequence::search` module is split into four submodules:

- `search::state` implements the `State` structure mentioned above.
- `search::history` implements the `History` of changes made to the state mentioned above.
- `search::leaf` provides fairly straightforward low-level operations on the information associated with leaves as part of a `State` object.
- `search::cherry` provides fairly straightforward low-level operation on the information associated with cherries as part of a `State` object.