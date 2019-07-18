# Synthetic Data and Experimental Results

This directory contains the synthetic data set used in our experiments and the experimental results obtained using this data set.

There are three directories:

- `inputs` contains the inputs we used in our experiments.
- `results` contains the raw data recording the results of our experiments.
- `tuning` contains the raw data recording the results of preliminary test runs used to determine the optimal parameters of `-w` and `-p` of `tc_seq` and for determining the effect of redundant branch elimination on the running time of the algorithm.

## Inputs

### tc_seq_performance_testing

These are the test inputs used for the various preliminary tuning tests and for testing how difficult synthetic inputs `tc_seq` can solve within 1 hour.  The files are named in the form `<t>_<i>.txt`, where *t* is the number of trees passed as argument to the `-t` option of the synthetic data generator.  See the description of the synthetic data generator in `code/data_gen/synthetic` for details.  *i* is a sequence number, that is, `<t>_<i>.txt` is the *i*th file we generated with parameter *t*.

### tc_seq_vs_hybroscale

These ar the test inputs used for the comparison between `tc_seq` and Hybroscale.  The naming of these files is identical to the files in `tc_seq_performance_testing`.

## Results

### tc_seq_performance_testing.txt

This file contains the timing results of all runs performed on the data in `inputs/tc_seq_performance_testing` using our `tc_seq` algorithm.  Each line in this file is of the format

```
input_name algorithm k level t1 t2 t3 timeout errorInFile
```

where

- `input_name` is the name of the file in `inputs/tc_seq_performance_testing` used for the run.
- `algorithm` is `timeLimit3600-Alg-p8-w100-r`, which means that `tc_seq` was run with a time limit of 3,600s, options `-p8` and `-w100` and using cluster reduction and redundant branch elimination. 
- `k` is the number of reticulations in the computed network.
- `level` is the level of the computed network.
- `t1`, `t2`, `t3` are the three times reported by the `time` utility: wall clock time, total CPU time across all threads, and system time.
- `timeout` is `True` if the run exceeded the time limit of 3,600s.  In this case, `t1`, `t2`, and `t3` are recorded as `9999`.
- `errorInFile` is `True` if there was some error loading the file (`False` in all instances).

### tc_seq_vs_hybroscale.txt

This file contains the timing results of all runs performed on teh data in `inputs/tc_seq_vs_hybroscale` using our `tc_seq` algorithm and Hybroscale.  The line format is the same as in `tc_seq_performance_testing.txt`, except that `input_name` refers to a file in `inputs/tc_seq_vs_hybroscale` and  `algorithm` can take on a second value, `Hybroscale`, which means that this line records the running time of Hybroscale on this particular input.

## Tuning

### test_p.txt

This file contains the timing results of test runs of `tc_seq` with different choices of the `-p` parameter (number of threads spawned by the algorithm).  The format of each line is the same as in `results/tc_seq_performance_testing.txt`.  The `input_name` field refers to the file with that name in `inputs/tc_seq_performance_testing`.  The algorithm name is of the form `algorithm-p<p>-w100-r`, which indicates that the algorithm was run with option `-w100`, with cluster reduction, and redundant branch elimination, and using *p* threads.

### test_w.txt

This file contains the timing results of test runs of `tc_seq` with different choices of the `-w` parameter (number of iterations between checks for work requests from other threads).  The format of each line is

```
input_name w t1 t2 t3
```

where

- `input_name` is the name of the file in `inputs/tc_seq_performance_testing` used for the run.
- `w`  is the value passed to the run as the `-w` option.
- `t1`, `t2`, `t3` are the three times reported by the `time` utility: wall clock time, total CPU time across all threads, and system time. 

### test_redundant_branch_elimination.txt

This file contains the timing results of test runs of `tc_seq` without redundant branch elimination, in order to compare it with the results obtained *with* redundant branch elimination.  The format of each line is the same as in `results/tc_seq_performance_testing.txt`.  The `input_name` field refers to the file with that name in `inputs/tc_seq_performance_testing`.  The algorithm name is  `timeLimit3600-Alg-pnative-w100`, which indicates that the algorithm was run with options `-pnative`,  `-w100`, with cluster reduction, but without redundant branch elimination.

