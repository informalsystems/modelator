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

```sh
$ modelator typecheck
Type checking OK ✅
```

Run `check` on the loaded model without specifying any property to check:

```sh
$ modelator check
...
[2]
```

Run `check` on the loaded model specifying a property to check:

```sh
$ modelator check --invariants=Inv
...
✅ Inv
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

Clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
