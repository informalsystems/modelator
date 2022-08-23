First make sure that there is no model loaded:

```sh
$ modelator reset
...
```

Load a model and a configuration from a toml file:

```sh
$ modelator load model/Test1.tla --config model/Test1.config.toml
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
Config at model/Test1.config.toml:
- config_file_path: None
- constants: {}
- examples: []
- init: Init
- invariants: ['Inv']
- next: Next
- params: {'cinit': None, 'config': None, 'length': 5, 'max_error': None, 'no_deadlock': True, 'view': None}
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
$ modelator check --invariants InvB --init=InitB --params length=3
...
✅ InvB
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
