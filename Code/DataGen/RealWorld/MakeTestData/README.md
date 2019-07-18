# Binary trees extracted from the Aquificae data set

## Generated data

The generated data is in the `data/` subdirectory.

This data was extracted from the Aquificae data set used in

Whidden, Zeh, Beiko.  Supertrees Based on the Subtree Prune-and-Regraft Distance.
_Systematic Biology_, 63(4):566-581, 2014.

## The code

The goal of the extraction code was to

- Extract binary trees with identical label sets,
- Extract as many trees as possible, and
- Resolve multifurcations in a way that preserves the "spirit" of the data, that is,
  as much as possible, without introducing bipartitions that disagree between trees.

This was done using the following procedure:

### Choosing Labels and Trees

We constructed a priority queue over the set of labels with the priority of
every label equal to the number of trees it occurs in.  Given the number of
leaves we want the extracted trees to have, we repeated the following `numLeaves` times:

- Choose the most frequent leaf.
- Delete all trees that do not contain this leaf.
- Decrease the occurrence counts of all leaves in the deleted trees so their new occurrence
  counts reflect their numbers of occurrences in the remaining trees.

Once this procedure finishes, we have a set labels and the set of all trees in
the input data set that contain these labels.  We compute the restriction of
every tree in this subset to the set of chosen labels.

### Resolving Multifurcations

In order to create trees that are "as consistent with each other as possible", we resolved
multifurcations in a way that does not increase the triplet distance between the trees too
much.  We repeated the following process until all trees were binary:

- Inspect the trees in order.
- For each tree, inspect its multifurcations in an arbitrary order.
- For each multifurcation, consider all pairs of children that can be resolved and count the
  number of resolved triplets (triplets of the form ab|c as opposed to a|b|c) that this
  introduces and which are also triplets of other trees in the current set of trees.

  - If there exists such a pair with at least one introduced triplet that agrees with another
    tree, then resolve the pair with the most introduced triplets that agree with other trees.
  - Otherwise, move on to the next multifurcation or the next tree.

- If the previous step resolved at least least one multifurcation, start another iteration.
  Otherwise, pick an arbitrary multifurcation in one of the trees and a random pair of
  children of this multifurcation and resolve it.  Then start the next iteration.
  (This random resolution will be matched by all other trees in the next iteration, thus
  forcing consistency between the trees.)
