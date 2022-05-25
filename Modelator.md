Modelator API & Shell
===

**NB! This is a WIP description for something that's not fully implemented yet!**

Modelator is a tool facilitating interaction with *models* (TLA+ models in particular): their construction, inspection, checking invariants, generating traces, and model-based testing.

Our aim is to make your modeling experience easy and enjoyable. For that we provide, in Python:
 - *Modelator API*, which allows to automate modeling tasks in tests and CI;
 - *Modelator Shell* provides, in addition to Modelator API, a set of interactive commands to be used in any Python shell, and allows to playfully explore and interact with models.

To use Modelator API in your Python code, do

```python
from modelator import *
```

and to use Modelator Shell in a Python Shell, do

```python
from modelator.shell import *
```

Many of the functions from Modelator API have their counterparts in Modelator Shell, with one important difference: API functions are always silent, and communicate via return values and exceptions, while Shell functions communicate via printing output.


## Model parsing

`Model` is a Python class representing a TLA+ model. Currently the only way to obtain a model is to parse it from a TLA+ source file or text.

```python
from modelator import *

m = parse_model("samples/HelloWorld.tla")

m2 = parse_model_source('''
----- MODULE HelloWorld -----

EXTENDS Naturals
CONSTANTS
  \* @type: Int;
  MAX
VARIABLES 
  \* @type: Int;
  x
Init == x = 0
Next == x <= MAX /\ x' = x + 1
Inv  == x >= 0   /\ x<= MAX

=============================
''')
```

A model you obtain is always *correct by construction*. But what happens if the model file doesn't exist, or the model parses unsuccessfully? In that case, exceptions will be raised, so be prepared to handle them! 

Having obtained the model, you can inspect it:

```python
>>> m.name()
'HelloWorld'
>>> m.constants()
['MAX']
>>> m.variables()
['x']
>>> m.operators()
['Init', 'Next', 'Inv']
>>> m == m2
True
```

Modelator Shell also has `parse_model()` command, which is silent on success, but will print some useful information on error. E.g., try to add a comma after the declaration of variable `x`, and then:

```sh
python
>>> from modelator.shell import *
>>> m = parse_model("samples/HelloWorld.tla")
Parse error at ./samples/HelloWorld.tla:10:
Was expecting "Identifier"
Encountered "Beginning of definition" at line 10, column 1 and token ","
```

Modelator Shell provides you additionally with the `autoparse_model()` command: it has the same functionality as `parse_model()`, but additionally, in the background, keeps re-parsing the file whenever it changes on the disk. This is useful when you are writing a new model, or modifying an existing one: keep the terminal with Modelator Shell and auto-parsing open, and get notifications whenever there is any syntax problem in the model.