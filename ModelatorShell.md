# Modelator Shell

Shell is giving users an interactive way to experiment with Modelator.

## Starting the shell

Run `python -i modelator_shell.py`.

## Usage examples

Run `m = ModelatorShell()`.
Variable `m` now holds an instance of modelator.
We get the basic info about the instance by typing into the shell `m` (more detailed) or `print(m)` (prettier).
By typing `help(m)` or `help(ModelatorShell)`, we get the info on how to use the `ModelatorShell` class.

The function `load` loads the model file (get all the info by typing `help m.load`).
For instance, type `m.load('modelator/samples/Hello.tla')`.
With the file loaded, `ModelatorShell` will make sure to reload it before calling any other action.
(This is the default behavior, can be changed by setting `m.autoload` to `False`.)

Calling `m.parse()` will parse the currently loaded file.
In our case it will return `File modelator/samples/Hello.tla successfully parsed.`.
Feel free to modify the file `Hello.tla`.
For instance, by adding a comma after the declaration of variable `x`.
In this case, `m.parse()` should return

```
Parse error at <path>modelator/samples/Hello.tla:11:
Was expecting "Identifier"
Encountered "Beginning of definition" at line 11, column 1 and token ","
```

If using the shell inside VSCode editor, you can click on the specific location of the error
and it will open the place where the problem is detected.

You can use the command `m.typecheck()` the same way.

The last command to use is `m.check()`.
If run without arguments, it will assume the default arguments:

- that the initial state predicate is 'Init',
- that the next state predicate is 'Next',
- that the list of invariants to check is ['Inv'],
- and that the checker is `apalache`

We could suply each of these arguments individually, for instance
`m.check(invariants=['Inv', 'Inv2'], checker='tlc')`.
The output is

```
Check error at modelator/samples/Hello.tla:
Invariant Inv violated.
Counterexample is [{'x': 'hello', 'y': 22}, {'x': 'world', 'y': 20}]
```

We could also give the name of the config file as an argument, as in
`m.check(config_file_name='Hello.cfg')`.
