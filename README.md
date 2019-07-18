# Computing Optimal Tree-Child Networks for Sets of Binary Phylogenetic Trees

This is all the supporting code and test data for the paper

> **A Practical Fixed-Parameter Algorithm for Constructing Tree-Child Networks from Multiple Binary Trees**  
> *Leo van Iersel, Remie Janssen, Mark Jones, Yukihiro Murakami, and Norbert Zeh*

The repository is organized as follows:

* `code`: All code used for the experiments
  * `tree_child`: Implementation of the algorithm described in the paper
  * `data_gen`: Various helper programs used to generate or transform the test data used in the paper
    * `real_world`: The code used to extract binary trees over the same label set from a large set of multifurcating trees with different label sets
    * `synthetic`: Generator of random synthetic inputs
* `data`: The input data used for the experiments in the paper and experimental results
  * `inputs`: Data sets used in the experiments
    * `real_world`: Real-world data sets
    * `synthetic`: Synthetic data sets
  * `results`: Experimental results

For more detailed descriptions of the contents of the different directories, see the READMEs in those directories.
