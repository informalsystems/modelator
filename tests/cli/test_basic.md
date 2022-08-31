First make sure that there is no model loaded:

```sh
$ modelator reset
...
```

Commands that should print a message when there is no model loaded:

```sh
$ modelator info
Model file does not exist
$ modelator typecheck
Model file does not exist
$ modelator reload
ERROR: model not loaded; run `modelator load` first
```

Running `load` without passing a path will exit with an error code:

```sh
$ modelator load
...
[2]
```
