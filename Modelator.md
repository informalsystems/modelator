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


## Models & parsing

`Model` is a Python class representing a TLA+ model. Currently the only way to obtain a model is to parse it from a TLA+ source file or source text. As our first example we use the (slightly simplified) [HourClock](modelator/samples/HourClock.tla) TLA+ model from the book [Specifying Systems](https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf) by Leslie Lamport; we've only extended this model with [type annotations of the Apalache model checker](https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html).

```python
from modelator import *

m = parse_model("samples/HourClock.tla")

m2 = parse_model_source('''
----- MODULE HourClock -----

EXTENDS Naturals, Sequences
VARIABLES 
  \* @typeAlias: STATE = [ hr: Int ];
  \* @type: Int;
  hr
Init == hr \in (1..12)
Next == hr' = IF hr /= 12 THEN hr + 1 ELSE 1

============================
''')
```

A model you obtain is always *correct by construction*. But what happens if the model file doesn't exist, or the model parses unsuccessfully? In that case, exceptions will be raised, so be prepared to handle them! 

Having obtained the model, you can inspect it:

```python
>>> m.name()
'HourClock'

>>> m.variables()
['hr']
>>> m.operators()
['Init', 'Next']
>>> m == m2
True
```

Modelator Shell also has `parse_model()` command, which is silent on success, but will print some useful information on error. E.g., try to add a comma after the declaration of variable `x`, and then:

```sh
python
>>> from modelator.shell import *
>>> m = parse_model("samples/HourClock.tla")
Parse error at ./samples/HourClock.tla:8:
Was expecting "Identifier"
Encountered "Beginning of definition" at line 8, column 1 and token ","
```

Modelator Shell provides you an additional layer of functionality compared to Modelator API: *update tracking*. Issuing the command `track_model_updates()` will force Modelator to track any changes files, from which the model was parsed; in the above case, upon any changes to the `"samples/HelloWorld.tla"` file, the model will be re-parsed, and the variable `m` will be updated. This is useful when you are writing a new model, or modifying an existing one: keep the terminal with Modelator Shell and update tracking open, and get notifications whenever there is any syntax problem in the model. To stop tracking updates, issue the `untrack_model_updates()` command.

## Examples, Invariants, Tests

Having a model in place, what can you do with it? We identify three main possibilities: exploration of examples (sampling), verification (invariant checking), and testing (generation and execution of tests).

### Sample examples

A model represents an abstraction: some aspect of a system, that we've managed to understand and write down in a formal manner. The first thing we might want to do with a model, is to assure ourselves that it functions as intended. For that purpose we formulate example assertions, and can ask `Modelator` to sample them, i.e. to provide concrete instances that satisfy these example assertions. Such instances are called _traces_: sequences of system steps, starting from the initial system state, and following the rules of system evolution at each step.

Closely following the classification outlined in [Apalache manual on invariant types](https://apalache.informal.systems/docs/apalache/principles/invariants.html), we allow to sample *state*, *action*, and *trace* examples; please refer to the Apalache manual on how to specify them. Below we use the `HourClock` model, for which we give would like to sample some examples; here are the examples from [HourClockTraits.tla](modelator/samples/HourClockTraits.tla):

```tla
----- MODULE HourClockTraits -----

EXTENDS HourClock

ExThreeHours == hr = 3

ExHourDecrease == hr' < hr

\* @type: Seq(STATE) => Bool;
ExFullRun(trace) == 
    /\ Len(trace) = 12
    /\ \A s1, s2 \in DOMAIN trace: 
           s1 /= s2 => trace[s1].hr /= trace[s2].hr
        

==================================
```

Here are some explanations on the above examples:
- State example `ExThreeHours` asks to produce a trace that reaches a state where the clock shows three hours;
- Action example `ExHourDecrease` asks to produce a trace that reaches an action, which decreases the hour that clock shows;
- Trace example `ExFullRun` asks to produce a trace of length 12, such that all hours shown in the trace states are pairwise distinct.

Modelator makes it easy for you to sample examples. It employs the convention, that any operator prefixed or suffixed with "Ex" or "Example", represents an example. The `sample()` command allows to sample either an explicitly specified example, or, by default, it samples all auto-collected examples.

```sh
python
>>> from modelator.shell import *
>>> m = parse_model("samples/HourClockTraits.tla")
>>> m.sample()
Example for "ExThreeHours": 
  hr = 3
Example for "ExHourDecrease": 
  hr = 12 | hr = 1 
Example for "ExFullRun": 
  hr = 1 | hr = 2 | hr = 3 | hr = 4 | hr = 5 | hr = 6 | hr = 7
  hr = 8 | hr = 9 | hr = 10 | hr = 11 | hr = 12
```