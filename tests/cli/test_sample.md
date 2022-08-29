# Test the `sample` command

Run `sample` without specifying a model or a property to check should fail:

```sh
$ modelator sample
...
[1]
```

Run `sample` without specifying a model should fail:

```sh
$ modelator sample --examples=ThreeSteps
...
[1]
```

Run `sample` with a non existing config file should fail:

```sh
$ modelator sample --config-path non-existing-file
ERROR: config file not found
[4]
```

Run `sample` with ...:

```sh
$ modelator sample --model-path model/Test3.tla --examples ThreeSteps
...
- ThreeSteps OK ✅
...
```

Running `sample` on a property that is not defined in the model should fail:

```sh
$ modelator sample --model-path model/Test3.tla --examples=NonExistingProperty
...
ERROR: NonExistingProperty not defined in the model
...
[3]
```
