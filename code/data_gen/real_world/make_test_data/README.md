# Data Transformer for Real-World Data

Given that most real-world data consists of multifurcating trees and those trees often do not have the same label sets, this data is not suitable for testing code that can only handle binary trees and only trees with identical label sets.  This is some code that *heuristically*

1. Extracts as many trees as possible that share a given target number of leaves and
2. Resolves multifurcation in a way that tries to avoid introducing discordance between the trees resulting only from this resolution.

Details of the procedure used to do this are described below.

## How to Compile

To compile, you need an up-to-date Haskell compiler (ghc).  The code should compile fine with *vanilla ghc + cabal*, *Haskell platform* or *Haskell Stack*.  However, the only method "officially" supported at this point is using *Haskell Stack*.  Information on installing *Haskell Stack* can be found at [haskellstack.org]().

To compile (without installing), run

```bash
$ stack build
```
The built executable can then be found in
`.stack-work/install/x86_64-osx/lts-12.13/8.4.3/bin/MakeTestData-exe`.

To compile and also copy `MakeTestData-exe` to `$HOME/.local/bin`, run

```shell
$ stack install
```

## How to Run

Running

```shell
$ MakeTestData-exe
```

prints a brief usage message that lists the expected arguments:

```
USAGE: MakeTestData <leaf count> <input file> <output file>
```

- `leaf count` is the desired number of leaves the extracted trees should have.
- `input file` is the file that contains the set of multifurcating trees from which the binary trees are to be extracted.  This file must be in **Newick format**.
- `output file` is the file where the generated trees will be written.  Again, these trees will be written in **Newick format**.

The parser can handle labels on internal nodes as well as branch lengths as part of the input.  These labels and branch lengths are discarded in the output file.

## Description of the Algorithm

### Tree Extraction

The set of all labels is placed in a priority queue.  The priority of each label is the number of trees it occurs in.  The following step is then repeated `leaf count` times:

- Choose the most frequent leaf.
- Delete all trees that do not contain this leaf.
- Decrease the occurrence counts of all leaves in the deleted trees so their new occurrence
  counts reflect their numbers of occurrences in the remaining trees.

This produces a set of trees that (at least) share the chosen set of leaves.  The final step of the tree extraction procedure is to restrict each of the selected trees to the selected set of leaves (in order to ensure that all trees have the same label set).

### Tree Resolution

This step uses the triplet distance (the number of triplets that disagree between each pair of trees, summed over all pairs) between the chosen trees as the measure of discordance.  Each resolution step aims to increase the triplet distance as little as possible.  The tree resolution procedure repeats the following step until all trees are binary:

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
