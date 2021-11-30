---
title: Hello World
description: A minimal TLA+ spec
layout: default
parent: TLA+ Basics Tutorials
nav_order: 3
---

# 'Hello world' using TLC

**The .tla and other referenced files are included [here](https://github.com/informalsystems/modelator/tree/main/jekyll/docs/tla_basics_tutorials/models).**

Let's model a system with two processes Alice and Bob. They are connected by a network that can lose and reorder messages. Alice will send two messages "hello" and "world" to Bob in an undetermined order. If Bob receives "hello" and then "world" he will become happy.

hello_world.tla contains the model and hello_world.cfg contains the configuration file needed to model check it using TLC.

Let's unpack the body of the .tla file.

## Boilerplate

You should write TLA in between two lines as below. This is an artifact of the module system.

```tla
---- MODULE hello_world ----
\* content here...
====
```

We extend (import) a modules from the standard library

```tla
EXTENDS Sequences \* Import Sequences module from the standard library
```

it provides the Sequence data structure. It is a list.

## The state machine

In TLA+ you define a state machine. There is an initial state, which is a choice of values for each variable declared. You also define the transitions allowed in the system.

We model 4 pieces of state: Alice's outbox, the messages in the network, Bob's mood and Bob's inbox.

```tla
VARIABLES
    alices_outbox,
    network,
    bobs_mood,
    bobs_inbox
```

The Init _operator_ defines the initial values of the state variables of the model. In TLA+ the term operator is used to mean something like a programming language function. Please take the Init operator on faith right now.

```tla
Init ==
    /\ alices_outbox = {} \* Alice has sent nothing (empty set)
    /\ network = {} \* AND so is the network
    /\ bobs_mood = "neutral" \* AND Bob's mood is neutral
    /\ bobs_inbox = <<>> \* AND Bob's inbox is an empty Sequence (list)
```

State machine transitions are pairs: (CurrentState, NextState). In TLA+ you describe the transitions allowed in the system by writing a boolean function over pairs (CurrentState, NextState). If a pair makes your boolean function evaluate true then the model checker will check that transition. In fact, the model checker will check **all** transitions that match your boolean function. This is what allows the model checker to exhaustively explore system behavior.

_Practically_ this means that you define transitions by writing _actions_: operators that take into account the CurrentState and the NextState. Because the variable names are the same in both states, you denote the NextState variables by appending the **'** character to identifiers. In TLA+ you write actions OR'ed together in the Next operator.


```tla
Next ==
    \/ AliceSend("hello")
    \/ AliceSend("world")
    \/ NetworkLoss
    \/ NetworkDeliver
    \/ BobCheckInbox
```

```tla
AliceSend(m) == 
    /\ m \notin alices_outbox
    /\ alices_outbox' = alices_outbox \union {m}
    /\ network' = network \union {m}
    /\ UNCHANGED <<bobs_mood, bobs_inbox>>

NetworkLoss == 
    /\ \E e \in network: network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, bobs_inbox, alices_outbox>>

NetworkDeliver == 
    /\ \E e \in network:
        /\ bobs_inbox' = bobs_inbox \o <<e>> 
        /\ network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, alices_outbox>>

BobCheckInbox == 
    /\ bobs_mood' = IF bobs_inbox = <<"hello", "world">> THEN "happy" ELSE "neutral"
    /\ UNCHANGED <<network, bobs_inbox, alices_outbox>>
```

Pretend we are the model checker and we are currently 'looking' at the CurrentState _C_. We compute all possible NextState's _N_, but we only consider  a candidate _N_ to be valid if Next is true when evaluated over the pair (_C_, _N_). Since Next is the OR'ing of actions, the pair will make Next true if it makes at least one of the actions true.

Inspect the AliceSend(m) action for example.

```tla
AliceSend(m) == 
    /\ m \notin alices_outbox
    /\ alices_outbox' = alices_outbox \union {m}
    /\ network' = network \union {m}
    /\ UNCHANGED <<bobs_mood, bobs_inbox>>
```

In English the action says this

"I am true when: \
my argument _m_ is not in the set _alices_outbox_ in the CurrentState \
AND _alices_outbox_ in the NextState is the same as it is in the CurrentState, but with _m_ included\
AND _network_ in the NextState is the same as it is in the CurrentState, but with _m_ included\
AND _bobs_mood_ doesn't change between the CurrentState and NextState\
AND _bobs_inbox_ doesn't change between the CurrentState and NextState
"

We must include the UNCHANGED keyword - there is no ambiguity in TLA+!

Consider NetworkLoss

```tla
NetworkLoss == 
    /\ \E e \in network: network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, bobs_inbox, alices_outbox>>
```

This action is more advanced: it contains the '\\E' (there exists) syntax. It says

"I am true when:\
There is an element e in the _network_ of the CurrentState, and that element is not in the _network_ of NextState\
AND _bobs_mood_ doesn't change between the CurrentState and NextState\
AND ...
"

Let's consider how a model checker could select a transition, given a current state where

```
alices_outbox = {"hello"}
network = {"hello"}
\* ignore bobs variables for now
```

knowing that Next is 

```tla
Next ==
    \/ AliceSend("hello")
    \/ AliceSend("world")
    \/ NetworkLoss
    \* (ignore other operators for now)
```

In a pair (CurrentState, NextState) where AliceSend("world") was true NextState must look like

```
alices_outbox = {"hello", "world"}
network = {"hello", "world"}
\* ignore bobs variables for now
```

and in one where NetworkLoss was true NextState would look like 

```
alices_outbox = {"hello"}
network = {}
\* ignore bobs variables for now
```

Next evaluates to true for both of these pairs, and the model checker will check _both_ possibilities for us.

Understanding Next as a boolean function over pairs of states is key. The Init operator is a special case, it's a boolean function over one state only. (It's not a special case if you consider it to be a boolean function over a pair (IgnoredState, InitialState) for a hidden IgnoredState).

We have looked at AliceSend and NetworkLoss. Let's look at NetworkDeliver and BobCheckInbox.

```tla
NetworkDeliver == 
    /\ \E e \in network:
        /\ bobs_inbox' = bobs_inbox \o <<e>> 
        /\ network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, alices_outbox>>
```

NetworkDeliver matches transitions where an element e is removed from the network set and added (with the \\o operator) to bobs_inbox list.

```tla
BobCheckInbox == 
    /\ bobs_mood' = IF bobs_inbox = <<"hello", "world">> THEN "happy" ELSE "neutral"
    /\ UNCHANGED <<network, bobs_inbox, alices_outbox>>
```

As a challenge try to write BobCheckInbox (above) using only the logical operators /\ and \\/.

Answer:

```tla
BobCheckInbox == 
    /\ \/ /\ bobs_mood' = "happy"
          /\ bobs_inbox = <<"hello", "world">>
       \/ /\ bobs_mood' = "neutral"
          /\ bobs_inbox # <<"hello", "world">>
    /\ UNCHANGED <<network, bobs_inbox, alices_outbox>> 
```

## Checking Invariants

We modeled the state machine so now we can check what properties it has.

We can use a model checker to get sample execution traces beginning from the initial state and leading up to some state satisfying some boolean function. Precisely: we can find an sequence of states (T) starting in the initial state and ending in a state S that makes a boolean function P evaluate to true.

In common terminology the sequence of states T is called a counterexample, and the boolean function is the negation of an Invariant. This means if we want to find an execution T whose final state satisfies P we write an invariant: Inv == ~P and we check that. (We check that Inv always holds: if it doesn't then there exists a state where ~Inv = ~~P = P holds).

If we want to make sure that no execution exists whose final state satisfies P we write an invariant: Inv == P and we hope that the model checker exhausts its search without finding a trace.

Suppose we want to ensure that every (\\A means 'for all' in TLA+) message in the network was at some point sent by Alice.

```tla
NothingUnexpectedInNetwork == \A e \in network: e \in alices_outbox
```

NothingUnexpectedInNetwork is a boolean function over a single state. Using the model checker we can check it as an invariant.

We use the following configuration for TLC (hello_world.cfg)

```tla
INIT Init
NEXT Next

INVARIANTS
NothingUnexpectedInNetwork
```

We can check this using the VSCode plugin for TLA (through the context menu), or with

```bash
java -cp tla2tools.jar tlc2.TLC -config hello_world.cfg -workers auto -cleanup hello_world.tla

# TLC output:
# ...
# Model checking completed. No error has been found.
```

TLC should report no error found: this means that NothingUnexpectedInNetwork was also true in every execution.

We may be interested to find an execution where Bob becomes happy. We write the invariant

```tla
NotBobIsHappy == 
    LET BobIsHappy == bobs_mood = "happy"
    IN ~BobIsHappy
```

which makes use of the _LET_ keyword, used to define values or operators inline. 

We use the .cfg file

```tla
INIT Init
NEXT Next

INVARIANTS
NotBobIsHappy
```

We ask TLC to check if 'always NotBobIsHappy'. If Bob ever becomes happy then it will be false, so TLC will give us a counterexample, or trace, where Bob becomes happy.

TLC should spit out a trace

```
Error: Invariant NotBobIsHappy is violated.
Error: The behavior up to this point is:
State 1: <..>
/\ network = {}
/\ alices_outbox = {}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"

State 2: <..>
/\ network = {"hello"}
/\ alices_outbox = {"hello"}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"

State 3: <..>
/\ network = {"hello", "world"}
/\ alices_outbox = {"hello", "world"}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"

State 4: <..>
/\ network = {"world"}
/\ alices_outbox = {"hello", "world"}
/\ bobs_inbox = <<"hello">>
/\ bobs_mood = "neutral"

State 5: <..>
/\ network = {}
/\ alices_outbox = {"hello", "world"}
/\ bobs_inbox = <<"hello", "world">>
/\ bobs_mood = "neutral"

State 6: <..>
/\ network = {}
/\ alices_outbox = {"hello", "world"}
/\ bobs_inbox = <<"hello", "world">>
/\ bobs_mood = "happy"
```

Notice that bob is happy in state 8.

## Wrapping up

### This tutorial

1. How to read and write simple TLA+ 
2. How to structure models with the (boilerplate, variables, Init, Next, .cfg) pattern
3. How to think about transitions in terms of (CurrentState, NextState) pairs
4. How to use _actions_ to specify transitions in the Next operator
5. How to generate traces matching behaviors using TLC

That's it, congratulations :) Try the next tutorial.