# Test parsing errors

## Run `load` and `typecheck` on a model is not syntactically valid

```sh
$ modelator reset
...
$ modelator load model/errors/TestError1.tla
...
Parsing error 💥
...
[5]
```

## Run `check` and `sample` on a model that is not syntactically valid

```sh
$ modelator check --model-path model/errors/TestError1.tla --invariants Inv
...
Parsing error 💥
...
[5]
```

```sh
$ modelator sample --model-path model/errors/TestError1.tla --examples Inv
...
Parsing error 💥
...
[5]
```
