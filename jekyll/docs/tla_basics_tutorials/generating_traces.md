---
title: Generating Traces
description: How to generate execution traces from models
layout: default
parent: TLA+ Basics Tutorials
nav_order: 7
---

# Generating traces for automated testing using Apalache

**The .tla and other referenced files are included [here](https://github.com/informalsystems/modelator/tree/main/jekyll/docs/tla_basics_tutorials/models).**

Apalache allows you to generate more than one trace that satisfies a given behavior specified by a [state invariant](https://apalache.informal.systems/docs/tutorials/symbmc.html?highlight=invariant#invariants) or [trace invariant](https://apalache.informal.systems/docs/apalache/principles/invariants.html?highlight=trace#trace-invariants).

Generating multiple traces can be useful because different traces may give you insight into your system. There may be several different methods of exploiting the same vulnerability, for example. Generating multiple traces is also useful for [model-based testing](https://mbt.informal.systems/docs/modelator.html), where the goal is to use a model to generate tests for a software implementation of the system.

This tutorial shows you 

- How to use Apalache to generate multiple traces
- How to control the way that traces differ using Apalache's [VIEW](https://apalache.informal.systems/docs/apalache/principles/enumeration.html?highlight=View#enumerating-counterexamples) feature

The tutorial builds on the skills gained in ['Hello World'](./hello_world) and ['Ethereum'](./ethereum) where we model checked state and trace invariants but only generated a single trace.

## Demonstrating multiple traces

For instruction purposes we will use a small and simple model.

```tla
---- MODULE multiple_traces ----

EXTENDS Integers, Sequences, Apalache, typedefs

VARIABLES
    \* @type: Str;
    auxiliary_str,
    \* @type: Int;
    important_int

Init ==
    /\ auxiliary_str = "foo"
    /\ important_int = 0

ChangeAuxiliaryStr == 
    /\ auxiliary_str' \in {"foo", "bar", "wiz"}
    /\ UNCHANGED important_int
        
AddToImportantInt == 
    /\ UNCHANGED auxiliary_str
    /\ \E x \in 1..4 : important_int' = important_int + x

Next ==
    \/ ChangeAuxiliaryStr
    \/ AddToImportantInt

\* @type: () => Bool;
ImportantIntIs6 == 
    LET Behavior == important_int = 6
    IN ~Behavior

\* @type: Seq(STATE) => Bool;
ImportantIntIsOddUntil6(trace) ==
    LET Behavior ==
        /\ trace[Len(trace)].important_int = 6
        /\ \A i \in DOMAIN trace : 
            \/ (i = 1 \/ i = Len(trace))
            \/ trace[i].important_int % 2 = 1
    IN ~Behavior

View == important_int

====
```

Remember that to use trace invariants we must define a STATE type alias in typdefs.tla
```tla
---- MODULE typedefs ----

(*
  @typeAlias: STATE = [
    auxiliary_str : Str,
    important_int : Int
  ];
*) 

include_typedefs == TRUE
====
```

### Defining a View operator

The model contains two state variables. Suppose that auxiliary_str represents some data in your system that's needed for bookkeeping, but won't have an effect on the interesting behaviors. Suppose also that important_int contains some highly critical data.

The goal is to generate traces which differ only by the value of important_int in each state. Apalache's [VIEW](https://apalache.informal.systems/docs/apalache/principles/enumeration.html?highlight=View#enumerating-counterexamples) feature lets you define an operator named View taking all state variables and outputting some value. Apalache ensures that all pairs of generated traces t1 and t2 differ on the value of that function for at least one state.

By writing

```tla
View == important_int
```

we ensure that all the traces generated will have a different sequence of values for important_int.

### Our Invariants

The model contains operators defining the inverses of two behaviors we would like to generate traces for.

The state invariant ImportantIntIs6 will evaluate to false in any state where important_int is 6.

```tla
\* @type: () => Bool;
ImportantIntIs6 == 
    LET Behavior == important_int = 6
    IN ~Behavior
```

If we use Apalache to check ImportantIntIs6 it will find a single trace where the operator evaluates to false: meaning that the integer is 6.

```bash
apalache check --inv=ImportantIntIs6 multiple_traces.tla

# Apalache output:
# ... 
# State 2: Checking 1 trace invariant(s)                            
# State 2: trace invariant 0 violated. Check the counterexample in: counterexample1.json
# Found 1 error(s)                                                 
# The outcome is: Error
```

```tla
\* counterexample1.json

(* Initial state *)
State0 == auxiliary_str = "foo" /\ important_int = 0

(* Transition 1 to State1 *)
State1 == auxiliary_str = "foo" /\ important_int = 3

(* Transition 1 to State2 *)
State2 == auxiliary_str = "foo" /\ important_int = 6
```

This is useful but we can generate more traces by running

```bash
apalache check --inv=ImportantIntIs6 --max-error=3 --view=View multiple_traces.tla

# Apalache output:
# ... 
# State 2: Checking 1 state invariants 
# State 2: state invariant 0 violated. Check the counterexample in: counterexample1.json
# State 2: state invariant 0 violated. Check the counterexample in: counterexample2.json
# State 2: state invariant 0 violated. Check the counterexample in: counterexample3.json
# Found 3 error(s)                     
# The outcome is: Error
```

You should see three traces similar to the below

```tla
\* counterexample1.json

(* Initial state *)
State0 == auxiliary_str = "foo" /\ important_int = 0

(* Transition 1 to State1 *)
State1 == auxiliary_str = "foo" /\ important_int = 2

(* Transition 1 to State2 *)
State2 == auxiliary_str = "foo" /\ important_int = 6

\* counterexample2.json

(* Initial state *)
State0 == auxiliary_str = "foo" /\ important_int = 0

(* Transition 1 to State1 *)
State1 == auxiliary_str = "foo" /\ important_int = 3

(* Transition 1 to State2 *)
State2 == auxiliary_str = "foo" /\ important_int = 6

\* counterexample3.json

(* Initial state *)
State0 == auxiliary_str = "foo" /\ important_int = 0

(* Transition 1 to State1 *)
State1 == auxiliary_str = "foo" /\ important_int = 4

(* Transition 1 to State2 *)
State2 == auxiliary_str = "foo" /\ important_int = 6
```

Notice how they differ in the sequence of the important_int variable.


We can also generate multiple traces for the trace operator ImportantIntIsOddUntil6

```tla
\* @type: Seq(STATE) => Bool;
ImportantIntIsOddUntil6(trace) ==
    LET Behavior ==
        /\ trace[Len(trace)].important_int = 6
        /\ \A i \in DOMAIN trace : 
            \/ (i = 1 \/ i = Len(trace))
            \/ trace[i].important_int % 2 = 1
    IN ~Behavior
```

If we check the operator as an invariant Apalache will generate traces whose behavior matches the inline Behavior operator. The behavior operator matches traces where important_int has a value 6 in the last state, and odd values for all states except the Init state and the last state.

```bash
apalache check --inv=ImportantIntIsOddUntil6 --max-error=10 --view=View multiple_traces.tla

# Apalache output:
# ... 
State 2: Checking 1 trace invariant(s)                            
State 2: trace invariant 0 violated. Check the counterexample in: ...
Step 3: picking a transition out of 2 transition(s)               
State 3: Checking 1 trace invariant(s)                            
State 3: trace invariant 0 violated. Check the counterexample in: ...
...
State 3: trace invariant 0 violated. Check the counterexample in: ...
Step 4: picking a transition out of 2 transition(s)               
State 4: Checking 1 trace invariant(s)                            
State 4: trace invariant 0 violated. Check the counterexample in: ...
...
State 4: trace invariant 0 violated. Check the counterexample in: ...
Found 10 error(s)                                                 
The outcome is: Error                                             
```

Try inspecting the counterexample.tla files in the _apalache-out directory. Also try playing around with different invariants and particularly different View operators. For example, what do you think will happen if you specify

```tla
View == <<auxiliary_str, important_int>>
```

or 

```tla
View == 3 < important_int
```


## Wrapping up

### This tutorial

1. Why it's useful to generate multiple traces
2. Differentiating traces with a _View_ operator
3. Generating multiple traces for a state invariant
4. Generating multiple traces for a trace invariant

That's it. Congratulations for completing the basic tutorial set :)

### Further resources

- [model-based testing](https://mbt.informal.systems/docs/modelator.html) with modelator
- Documentation: [state invariants](https://apalache.informal.systems/docs/tutorials/symbmc.html?highlight=invariant#invariants)
- Documentation: [trace invariants](https://apalache.informal.systems/docs/apalache/principles/invariants.html?highlight=trace#trace-invariants)
- Documentation: [VIEW](https://apalache.informal.systems/docs/apalache/principles/enumeration.html?highlight=View#enumerating-counterexamples)
