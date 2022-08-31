# Test the `sample` command

Running `sample` without specifying a model or a property to check should fail:

```sh
$ modelator sample
...
[1]
```

Running `sample` without specifying a model should fail:

```sh
$ modelator sample --examples=ThreeSteps
...
[1]
```

Running `sample` with a non existing config file should fail:

```sh
$ modelator sample --config-path non-existing-file
ERROR: config file not found
[4]
```

Running `sample` with a model and a property to sample should succeed:

```sh
$ modelator sample --model-path model/Test3.tla --examples ThreeSteps
...
- ThreeSteps OK ✅
...
```

Check that the number and length of the generated trace files are as expected:

```sh
$ ./traces_num_generated.sh
1
$ ./traces_last_generated.sh | xargs -I {} ./traces_length.sh {}
3
```

Running `sample` with a model and a property to sample should succeed and generate 3 trace files:

```sh
$ modelator sample --model-path model/Test3.tla --examples ThreeSteps --max_error=3
...
- ThreeSteps OK ✅
...
```

Check that the number and length of the generated trace files are as expected:

```sh
$ ./traces_num_generated.sh
3
$ ./traces_last_generated.sh | xargs -I {} ./traces_length.sh {}
3
```

Running `sample` on a property that is not defined in the model should fail:

```sh
$ modelator sample --model-path model/Test3.tla --examples=NonExistingProperty
...
ERROR: NonExistingProperty not defined in the model
...
[3]
```
