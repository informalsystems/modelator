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

Running `check` on the loaded model should succeed:

```sh
$ modelator check
...
- Inv OK ✅
...
```

Running `check` on the loaded model, while overriding the property to check and
passing some setting to the checker, should succeed:

```sh
$ modelator check --invariants InvB --init=InitB --length=3
...
- InvB OK ✅
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

Finally, clean the generated files after the test:

```sh
$ modelator reset
Model file removed
```
