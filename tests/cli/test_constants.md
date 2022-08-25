First make sure that there is no model loaded:

```sh
$ modelator reset
...
```

Load a model and type check it:

```sh
$ modelator load model/Test2.tla
...
Loading OK ✅
$ modelator typecheck
Type checking OK ✅
```

Running `check` on the loaded model, without initializing constants, should fail
with an error message:

```sh
$ modelator check --invariants Inv
...
- Inv FAILED ❌
    A constant in the model is not initialized
...
```

Running `check` on the loaded model passing `invariants` and valid `constants`
should succeed:

```sh
$ modelator check --invariants Inv --constants X=InstanceX
...
- Inv OK ✅
...
```

Running `check` on the loaded model passing `invariants` and invalid `constants`
should fail:

```sh
$ modelator check --invariants Inv --constants X=AnUndefinedIdentifier
...
- Inv FAILED ❌
    Configuration error:
...
```

Finally, clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
