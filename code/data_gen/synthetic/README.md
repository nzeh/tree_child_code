# Generator for Random Synthetic Binary Phylogenetic Trees

The code in this directory was used to generate sets of random binary phylogenetic trees for the experiments on synthetic data reported in the paper.  Details of the generation procedure are given below.

## How to Run

```shell
$ python RandomTreesMain.py -k <number of reticulations> -t <number of trees> -n <number of leaves> \
> <output file>
```

This attempts to generate a data set consisting of

- `number of trees` trees on
- `number of leaves` leaves and with
- an optimal tree-child network with `number of reticulations` reticulations.

The emphasis is on "attempts".  Given the way the trees are generated, the output may:

- Contain more than `number of leaves` leaves,
- Consist of fewer than `number of trees` trees, and
- Have an optimal network with fewer than `number of reticulations` reticulations.

## Description of the Algorithm

Each run of `RandomTreesMain.py` generates a set of trees over the same label set in two phases.  The first phase generates a tree-child network with approximately `number of leaves` leaves and approximately `number of reticulations` reticulations.  The second phase extracts a random set of up to `number of trees` trees that are displayed by this network.

### Network Generation

Let *n* = `number of leaves` and *k* = `number of reticulations`.  The network is initialized to be a tree with two leaves.  This leaves *s'* = *n* + *k* – 2 tree nodes and *k'* = *k* reticulations to be added.  As long as *s'* > 0 and *k'* > 0, the algorithm does the following:

- Let *M* be the set of leaves whose parents and siblings are tree nodes or leaves.
- If |*M*| < 2 or *M* contains only two leaves with the same parent, then add a tree node as described below.
- Otherwise, add a tree node with probability *s'* / (*s'* + *k'*) and a reticulation with probability *k'* / (*s'* + *k'*).

Once this loop terminates, we have *s'* = 0 or *k'* = 0.

- If *k'* = 0, add tree nodes until *s'* = 0.
- If *s'* = 0, add reticulations until *k'* = 0, |*M*| < 2 or *M* contains only two leaves with the same parent.

#### Adding a Tree Node

Choose one of the existing leaves *u* uniformly at random.  Add two new leaves *v* and *w* and make them children of *u*.  This increases the number of tree nodes by one and does not change the number of reticulations.

#### Adding a Reticulation

Repeatedly choose two leaves *u* and *v* from *M* uniformly at random until *u* and *v* have different parents.  Then merge *v* with *u* and add a new leaf *w* with parent *u*.  This increases the number of reticulations by one and does not change the number of tree nodes.

### Tree Generation

A random tree displayed by the generated network is obtained by deleting one of the two parent edges of each reticulation node in the generated network uniformly at random and then suppressing the resulting degree-2 nodes.

A set of `number of trees` random trees is obtained by repeating this procedure `number of trees` times.  The resulting set of trees may contain duplicates (or is in fact guaranteed to contain duplicates if `number of trees` exceeds 2^<sup><i>k</i></sup>, where *k* = `number of reticulations`).  The final set of possibly less than `number of trees` trees is obtained by eliminating duplicates from the set of generated trees.  For simplicity, tree identity is checked only by comparing the Newick strings of the generated trees, that is, the trees `(a,b)` and `(b,a)`, which are identical, are considered to be different.