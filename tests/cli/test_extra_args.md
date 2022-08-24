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

```sh
$ modelator typecheck
Type checking OK ✅
```

TODO: Modelator should return an error message; here it just throws an exception.
Run `check` on the loaded model, without initializing constants:

```sh
$ modelator check --invariants Inv
...
EXITCODE: ERROR (255)
...
KeyError: 'violation.tla'
...
```

Run `check` on the loaded model reading the `invariants` and `cinit` from the config file:

```sh
$ modelator check --config-path model/Test2.config.toml
...
- Inv OK ✅
...
```

Run `check` on the loaded model overriding the property to check and passing some setting to the checker:

```sh
$ modelator check --invariants Inv --cinit=ConstInit --length=2
...
- Inv OK ✅
...
```

Clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
