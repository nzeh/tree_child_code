# Real-World Data and Experimental Results

This directory contains the real-world data set used in our experiments and the experimental results obtained using this data set.

There are two directories:

- `inputs` contains the inputs we used in our experiments.
- `results` contains the raw data recording the results of our experiments.

## Inputs

### original

This is the original data set containing the trees from

>  R.G. Beiko. Telling the whole story in a 10,000-genome world. *Biology Direct* 6:34, 2011.

The data sets used in our experiments were extracted from the file `Beiko_trees/AllTrees_names.tre`.

### extracted

This directory contains a number of files of the form `<n>_leaves_<t>_trees.txt`.  Such a file contains *t* binary trees over the same set of *n* taxa.  These trees were extracted from the data in  `original/Beiko_trees/AllTrees_Names.tre` using the code in `code/data_gen/real_world` using the procedure described in that directory.

### used

These are the input files used in our experiments.  These files are named in the from `<n>_leaves_<t>_trees_<m>_trees_<i>.txt`.  There are 10 files (*i* = 1, …, 10) for each combination of *n*, *t*, and *m*.  Each such file contains *m* trees chosen uniformly at random from the file `extracted/<n>_leaves_<t>_trees.txt`.

## Results

The file `tc_seq_vs_hybroscale.txt` contains the timing results of all runs performed on the data in `inputs` using out `tc_net` algorithm and *Hybroscale*.  Each line in this file is of the format

```
input_name algorithm k level t1 t2 t3 timeout errorInFile
```

where

- `input_name` is the name of the file in `inputs/used` used for the run.
- `algorithm` is `Hybroscale` is Hybroscale was used and `timeLimit3600-Alg-p8-w100-r` when `tc_net` was run with a time limit of 3,600s, options `-p8` and `-w100` and using cluster reduction and redundant branch elimination. 
- `k` is the number of reticulations in the computed network.
- `level` is the level of the computed network.
- `t1`, `t2`, `t3` are the three times reported by the `time` utility: wall clock time, total CPU time across all threads, and system time.
- `timeout` is `True` if the run exceeded the time limit of 3,600s.  In this case, `t1`, `t2`, and `t3` are recorded as `9999`.
- `errorInFile` is `True` if there was some error loading the file (`False` in all instances).

