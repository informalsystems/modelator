First make sure that there is no model loaded:

```sh
$ modelator reset
...
```

Load a model:

```sh
$ modelator load model/Test2.tla
...
Loading OK ✅
...
```

```sh
$ modelator typecheck
Type checking OK ✅
```

Run `check` on the loaded model, without initializing constants, should fail
with an error message:

```sh
$ modelator check --invariants Inv
Results:
❌ Inv
    A constant in the model is not initialized
...
```

Run `check` on the loaded model passing `invariants` and valid `constants`
should succeed:

```sh
$ modelator check --invariants Inv --constants X=InstanceX
...
✅ Inv
...
```

Run `check` on the loaded model passing `invariants` and invalid `constants`
should fail:

```sh
$ modelator check --invariants Inv --constants X=AnUndefinedIdentifier
...
❌ Inv
...
```

Clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
