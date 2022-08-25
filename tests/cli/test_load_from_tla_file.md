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
$ modelator typecheck
Type checking OK ✅
```

Run `check` on the loaded model without specifying any property to check:

```sh
$ modelator check
...
[1]
```

Run `check` on the loaded model specifying a property to check:

```sh
$ modelator check --invariants=Inv
...
✅ Inv
...
```

Running `check` on a property that is not defined in the model will fail:

```sh
$ modelator check --invariants=NonExistingProperty
...
❌ NonExistingProperty
    Configuration error:
...
```

Clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
