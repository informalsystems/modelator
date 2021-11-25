---
title: Hello World
layout: default
parent: Tla+
grand_parent: Model Based Testing
---
# 'Hello world' using TLC

Let's model a system with two processes Alice and Bob. They are connected by a network that can lose and reorder messages. Alice will send three messages, 'a', 'b' and 'c' to Bob in an undetermined order. If Bob receives 'a' and then 'b' and then 'c' he will become happy.

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

We model 4 pieces of state: Alice's memory of which messages she has sent, the messages in the network, Bob's mood and Bob's inbox.

```tla
VARIABLES
    sent_by_alice,
    network,
    bobs_mood,
    bobs_inbox
```

The Init _operator_ defines the initial values of the state variables of the model. In TLA+ the term operator is used to mean something like a programming language function. Please take the Init operator on faith right now.

```tla
Init ==
    /\ sent_by_alice = {} \* Alice's memory of what she sent is the empty set
    /\ network = {} \* AND so is the network
    /\ bobs_mood = "neutral" \* AND Bob's mood is neutral
    /\ bobs_inbox = <<>> \* AND Bob's inbox is an empty Sequence (list)
```

**In TLA you describe which transitions are valid from the universe of all possible transitions using a boolean function**. This is probably the most confusing thing to get your around when learning TLA+.

A transition is a pair: (CurrentState, NextState). We write a boolean function/operator over the set of all values that (CurrentState, NextState) can take. Given a state CurrentState, the model checker will look for all NextStates's such that (CurrentState, NextState) evaluates to true. The boolean function is called Next.

```tla
Next ==
    \/ AliceSend("a")
    \/ AliceSend("b")
    \/ AliceSend("c")
    \/ NetworkLoss
    \/ NetworkDeliver
    \/ BobCheckInbox
```

```tla
AliceSend(m) == 
    /\ m \notin sent_by_alice
    /\ sent_by_alice' = sent_by_alice \union {m}
    /\ network' = network \union {m}
    /\ UNCHANGED <<bobs_mood, bobs_inbox>>

NetworkLoss == 
    /\ \E e \in network: network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, bobs_inbox, sent_by_alice>>

NetworkDeliver == 
    /\ \E e \in network:
        /\ bobs_inbox' = bobs_inbox \o <<e>> 
        /\ network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, sent_by_alice>>

BobCheckInbox == 
    /\ bobs_mood' = IF bobs_inbox = <<"a", "b", "c">> THEN "happy" ELSE "neutral"
    /\ UNCHANGED <<network, bobs_inbox, sent_by_alice>>
```

We can see that Next is the OR'ing (\\/ = logical OR in TLA.) of a number of operators, which are shown above. Operators can be parameterized, as in the case of AliceSend(m). The Next operator defines a boolean function over all (CurrentState, NextState) pairs. A subset of those pairs will make the function evaluate to true. The model checker will check all of the NextState's from all of the valid pairs.

Pretend we are the model checker and we are currently 'looking' at the state _C_. We will consider all possible states as the NextState, but we will only consider the state _N_, for example, to be valid, if Next is true when evaluated over the pair (_C_,_N_).

We share the same variable names between _C_ and _N_ so we add a dash (') to the end of variable names when we mean the variable in the NextState. It's called priming.

We can see that the operators that Next is made of contain these primed variables. Inspect AliceSend(m) for example.

```tla
AliceSend(m) == 
    /\ m \notin sent_by_alice
    /\ sent_by_alice' = sent_by_alice \union {m}
    /\ network' = network \union {m}
    /\ UNCHANGED <<bobs_mood, bobs_inbox>>
```

In English the operator says this

"I am true when: \
my argument _m_ is not in the set _sent_by_alice_ in the CurrentState \
AND _sent_by_alice_ in the NextState is the same as it is in the CurrentState, but with _m_ included\
AND _network_ in the NextState is the same as it is in the CurrentState, but with _m_ included\
AND _bobs_mood_ doesn't change between the CurrentState and NextState\
AND _bobs_inbox_ doesn't change between the CurrentState and NextState
"

We must include the UNCHANGED keyword - there is no ambiguity in TLA+!

Consider NetworkLoss

```tla
NetworkLoss == 
    /\ \E e \in network: network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, bobs_inbox, sent_by_alice>>
```

This operator is more advanced: it contains the '\\E' (there exists) operator. It says

"I am true when:\
There is an element e in the _network_ of the CurrentState, and that element is not in the _network_ of NextState\
AND _bobs_mood_ doesn't change between the CurrentState and NextState\
AND ...
"

Let's consider how a model checker could select a transition, given a current state where

```
sent_by_alice = {"a"}
network = {"a"}
\* ignore bobs variables for now
```

knowing that Next is 

```tla
Next ==
    \/ AliceSend("a")
    \/ AliceSend("b")
    \/ AliceSend("c")
    \/ NetworkLoss
    \* (ignore other operators for now)
```

In a pair (CurrentState, NextState) where AliceSend("b") was true NextState must look like

```
sent_by_alice = {"a", "b"}
network = {"a", "b"}
\* ignore bobs variables for now
```

and in one where NetworkLoss was true NextState would look like 

```
sent_by_alice = {"a", "b"}
network = {}
\* ignore bobs variables for now
```

Next evaluates to true over both of these pairs, and the model checker will check _both_ possibilities for us.

Understanding Next as a boolean function over pairs of states is key to understanding TLA+. The Init operator is a special case, it's a boolean function over one state only. (It's not a special case if you consider it to be a boolean function over a pair (SentinelState, InitialState) for a hidden SentinelState).

A common misinterpretation is to view TLA+ code as describing an imperative execution, where one statement precedes the next. In actuality you define boolean functions and other simple pure functions, there is no concept of execution or execution order.

We have looked at AliceSend and NetworkLoss. Let's look at NetworkDeliver and BobCheckInbox.

```tla
NetworkDeliver == 
    /\ \E e \in network:
        /\ bobs_inbox' = bobs_inbox \o <<e>> 
        /\ network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, sent_by_alice>>
```

NetworkDeliver matches transitions where an element e is removed from the network set and added (with the \\o operator) to bobs_inbox list.

```tla
BobCheckInbox == 
    /\ bobs_mood' = IF bobs_inbox = <<"a", "b", "c">> THEN "happy" ELSE "neutral"
    /\ UNCHANGED <<network, bobs_inbox, sent_by_alice>>
```

As a challenge try to write BobCheckInbox (above) using only the logical operators /\ and \\/.

Answer:

```tla
BobCheckInbox == 
    /\ \/ /\ bobs_mood' = "happy"
          /\ bobs_inbox = <<"a", "b", "c">>
       \/ /\ bobs_mood' = "neutral"
          /\ bobs_inbox # <<"a", "b", "c">>
    /\ UNCHANGED <<network, bobs_inbox, sent_by_alice>> 
```

## Checking Invariants

We modeled the state machine so now we can check what properties it has.

We can use a model checker to get sample execution traces beginning from the initial state and leading up to some state satisfying some boolean function. Precisely: we can find an sequence of states (T) starting in the initial state and ending in a state S that makes a boolean function P evaluate to true.

In common terminology the sequence of states T is called a counterexample, and the boolean function is the negation of an Invariant. This means if we want to find an execution T whose final state satisfies P we write an invariant: Inv == ~P and we check that. (We check that Inv always holds: if it doesn't then there exists a state where ~Inv = ~~P = P holds).

If we want to make sure that no execution exists whose final state satisfies P we write an invariant: Inv == P and we hope that the model checker exhausts its search without finding a trace.

Suppose we want to ensure that every (\\A means 'for all' in TLA+) message in the network was at some point sent by Alice.

```tla
NothingUnexpectedInNetwork == \A e \in network: e \in sent_by_alice
```

NothingUnexpectedInNetwork is a boolean function over a single state. Using the model checker we can check it as an invariant.

We use the following configuration for TLC

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

Using the above we ask TLC to check if 'always BobIsNotHappy'. If Bob ever becomes happy then it will be false, so TLC will give us a counterexample, or trace, in which Bob becomes happy.

TLC should spit out a trace

```
Error: Invariant NotBobIsHappy is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ network = {}
/\ sent_by_alice = {}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"
State 2: <..>
/\ network = {"a"}
/\ sent_by_alice = {"a"}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"
State 3: <..>
/\ network = {"a", "b"}
/\ sent_by_alice = {"a", "b"}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"
State 4: <..>
/\ network = {"a", "b", "c"}
/\ sent_by_alice = {"a", "b", "c"}
/\ bobs_inbox = <<>>
/\ bobs_mood = "neutral"
State 5: <..>
/\ network = {"b", "c"}
/\ sent_by_alice = {"a", "b", "c"}
/\ bobs_inbox = <<"a">>
/\ bobs_mood = "neutral"
State 6: <..>
/\ network = {"c"}
/\ sent_by_alice = {"a", "b", "c"}
/\ bobs_inbox = <<"a", "b">>
/\ bobs_mood = "neutral"
State 7: <..>
/\ network = {}
/\ sent_by_alice = {"a", "b", "c"}
/\ bobs_inbox = <<"a", "b", "c">>
/\ bobs_mood = "neutral"
State 8: <..>
/\ network = {}
/\ sent_by_alice = {"a", "b", "c"}
/\ bobs_inbox = <<"a", "b", "c">>
/\ bobs_mood = "happy"
```

Notice that bob is happy in state 8.

That's it, congratulations :) Try the next tutorial.
