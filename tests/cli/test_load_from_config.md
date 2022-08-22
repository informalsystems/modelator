First make sure that there is no model loaded:

```sh
$ modelator reset
...
```

Load model and configuration from a toml file:

```sh
$ modelator load model/Test1.config.toml
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
- operators: ['Init', 'Next', 'Inv', 'Inv2']
- variables: ['x']
Config:
- config_file_path: None
- constants: {}
- examples: []
- init: Init
- invariants: ['Inv']
- model_path: model/Test1.tla
- next: Next
- params: {'cinit': None, 'config': None, 'no_deadlock': True, 'length': 5, 'max_error': None, 'save_runs': False, 'view': None}
- traces_dir: traces/Test1
```

```sh
$ modelator typecheck
Type checking OK ✅
```

Run `check` on the loaded model:

```sh
$ modelator check
...
✅ Inv
...
```

Run `check` on the loaded model overriding the property to check and passing some setting to the checker:

```sh
$ modelator check --invariants Inv2 --params "length=3"
...
✅ Inv2
...
```

Running `check` on a property that is not defined in the model should fail:

```sh
$ modelator check --invariants=NonExistingProperty
...
ERROR: NonExistingProperty not defined in the model
...
[1]
```

Clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
