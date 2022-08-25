First make sure that there is no model loaded:

```sh
$ modelator reset
...
```

Load model from a TLA+ file:

```sh
$ modelator load model/Test1.tla
...
Loading OK ✅
...
$ modelator typecheck
Type checking OK ✅
```

```sh
$ modelator info
Model:
- constants: {}
...
- init: Init
- model_path: model/Test1.tla
- module_name: Test1
- monitors: []
- next: Next
- operators: ['Init', 'InitB', 'Next', 'Inv', 'InvB']
- variables: ['x']
```

Running `check` on the loaded model without specifying any property to check
should fail:

```sh
$ modelator check
...
[2]
```

Running `check` with a non existing config file should fail:

```sh
$ modelator check --config-path non-existing-file
ERROR: config file not found
[4]
```

Running `check` on the loaded model specifying a property to check should
succeed:

```sh
$ modelator check --invariants=Inv
...
- Inv OK ✅
...
```

Running `check` on a property that is not defined in the model should fail:

```sh
$ modelator check --invariants=NonExistingProperty
...
ERROR: NonExistingProperty not defined in the model
...
[3]
```

Finally, clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
