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
- operators: ['Init', 'Next', 'Inv']
- variables: ['x']
Config:
- config_file_path: None
- constants: {}
- examples: []
- init: Init
- invariants: ['Inv']
- model_path: model/Test1.tla
- next: Next
- params: {'cinit': None, 'config': None, 'no_deadlock': True, 'length': 20, 'max_error': None, 'save_runs': False, 'view': None}
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

Clean the generated files after the test:
```sh
$ modelator reset
Model file removed
```
