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
...
$ modelator typecheck
Type checking OK ✅
```

Check the output of `info`:

```sh
$ modelator info
Model:
- constants: {}
...
- init: Init
- model_path: model/Test2.tla
- module_name: Test2
- monitors: []
- next: Next
- operators: ['Init', 'Next', 'Inv', 'InstanceX', 'ConstInit']
- variables: ['x']
```

Running `check` on the loaded model, without initializing constants, should fail:

```sh
$ modelator check --invariants Inv
...
- Inv FAILED ❌
    A constant in the model is not initialized
...
```

Running `check` on the loaded model, while reading `invariants` and `cinit` from
the config file, should succeed:

```sh
$ modelator check --config-path model/Test2.config.toml
...
- Inv OK ✅
...
```

Running `check` on the loaded model overriding the property to check and passing
some setting to the checker should succeed:

```sh
$ modelator check --invariants Inv --cinit=ConstInit --length=2
...
- Inv OK ✅
...
```

Finally, clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
