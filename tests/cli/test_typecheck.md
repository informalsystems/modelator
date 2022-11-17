# Test type annotations in models

## Run `load` and `typecheck` on a model with incorrect type annotations

Loading a model that is syntactically correct but has incorrect type annotations
should succeed.

```sh
$ modelator reset
...
$ modelator load model/errors/TestError2.tla
...
Loading OK ✅
...
```

Then, the `typecheck` command should show an error message and fail.

```sh
$ modelator typecheck
Type checking error 💥
...
[6]
```

Clean the generated files after the test:

```sh
$ modelator reset
...
```

## Run `typecheck` on the model with type old-style type annotations (prior to Apalache 0.29)

```sh
$ modelator load model/transferLegacy.tla
...
```

First, run typecheck with no extra options.

```
$ modelator typecheck
Type checking error 💥
...
[6]
```

Then, run typecheck but with an extra option to enable legacy types.

```
$ modelator typecheck --features=no-rows
Type checking OK ✅
```

Clean the generated files after the test:

```sh
$ modelator reset
...
```

## Run `check` and `sample` on a model with incorrect type annotations

```sh
$ modelator check --model-path model/errors/TestError2.tla --invariants Inv
...
Type checking error 💥
...
```

```sh
$ modelator sample --model-path model/errors/TestError2.tla --tests Inv
...
Type checking error 💥
...
```

Clean the generated files after the test:

```sh
$ modelator reset
...
```
