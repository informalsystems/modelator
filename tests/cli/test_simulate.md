# Test the `simulate` command

First, reset the model.

```sh
$ modelator reset
...
```

Running `simulate` without a loaded model and without specifying any model path
should fail:

```sh
$ modelator simulate
...
[1]
```

Running `simulate` with a non existing config file should fail:

```sh
$ modelator simulate --config-path non-existing-file
ERROR: config file not found
[4]
```

Running `simulate` with an argument of a file should succeed.

```sh
$ modelator simulate --model-path model/Test1.tla
Simulating...
...
```

Running `simulate` with arguments specifying the number of simulations and their length.

```sh
$ rm -r test_tracesXX || true
...
```

```sh
$ modelator simulate --model-path model/Test1.tla --num-simulations 4 --simulation-length 3 --traces-dir test_tracesXX
Simulating...
...
```

Check that the number and length of the generated trace files are as expected:

```sh
$ ./simulation_traces_num_generated.sh test_tracesXX
4
$ ./simulation_traces_last_generated.sh test_tracesXX | xargs -I {} ./traces_length.sh {}
3
```
