# Test the `check` command

Running `check` without a loaded model and without specifying any model path
should fail:

```sh
$ modelator check
...
[1]
```

Running `check` with a non existing config file should fail:

```sh
$ modelator check --config-path non-existing-file
ERROR: config file not found
[4]
```

Running `check` trying to prove a property that is an invariant should succeed:

```sh
$ modelator check --model-path model/Test1.tla --invariants=Inv
...
- Inv OK ✅
...
```

Check that the number and length of the generated trace files are as expected:

```sh
$ ./traces_num_generated.sh Inv
1
$ ./traces_last_generated.sh Inv | xargs -I {} ./traces_length.sh {}
10
```

Running `check` trying to prove a property that is not an invariant should fail:

```sh
$ modelator check --model-path model/Test1.tla --invariants=InvB
...
- InvB FAILED ❌
    Check error:
...
    Trace: [(x = "a")]
...
```

Check that the number and length of the generated trace files are as expected:

```sh
$ ./traces_num_generated.sh InvB
1
$ ./traces_last_generated.sh InvB | xargs -I {} ./traces_length.sh {}
0
```

Running `check` trying to prove two properties:

```sh
$ modelator check --model-path model/Test1.tla --invariants Inv,InvC
...
- Inv OK ✅
...
- InvC OK ✅
...
```

Running `check` trying to prove two properties:

```sh
$ modelator check --model-path model/Test1.tla --invariants Inv,InvB
...
- Inv OK ✅
...
- InvB FAILED ❌
    Check error:
...
    Trace: [(x = "a")]
...
```

Check that the number and length of the generated trace files are as expected:

```sh
$ ./traces_num_generated.sh Inv
1
$ ./traces_last_generated.sh Inv | xargs -I {} ./traces_length.sh {}
10
$ ./traces_num_generated.sh InvB
1
$ ./traces_last_generated.sh InvB | xargs -I {} ./traces_length.sh {}
0
```

Running `check` on a property that is not defined in the model should fail:

```sh
$ modelator check --model-path model/Test1.tla --invariants=NonExistingProperty
...
ERROR: NonExistingProperty not defined in the model
...
[3]
```
