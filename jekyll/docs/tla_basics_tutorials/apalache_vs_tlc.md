---
title: Apalache vs TLC
description: Comparing model checkers
layout: default
parent: TLA+ Basics Tutorials
nav_order: 5
---

# Apalache vs TLC

In 'Hello World' we used TLC to model check a simple model. Both model checkers have advantages and disadvantages.

## Apalache

Apalache is a _bounded symbolic model checker_. Apalache will [transform](https://apalache.informal.systems/docs/apalache/theory.html) your Init and Next boolean functions into a logical formula which can be solved using an SMT solver. The formula is a conjunction of smaller formulas, one for each step of the system. This means Apalache requires a parameter _k_ specifying how many steps it should explore, starting from Init.

The advantage of Apalache's approach is that it can deal with some infinite state spaces. For example it can solve the constraint problem (x is integer) /\ (0 <= x) /\ (x < 2^32) very easily - providing concrete values of x that satisfy the constraints. Can you see how this may be useful for modelling financial transaction software?

The disadvantage of Apalache's approach is that it can not easily check executions which take many steps from Init. This is because the formula grows for each step in the execution, becoming progressively more difficult to solve with an SMT solver. In practice 6-12 steps may be achievable in a reasonable time, depending on the model.

## TLC

TLC is an _explicit state enumeration model checker_. TLC will perform a breadth first search of the state space starting from the Init state. Each explored state is fingerprinted and the fingerprint is stored. When a state is processed from the queue (BFS style) TLC will only explore its successor states if its fingerprint has not been seen before.

The advantage of TLC's approach is that it can check unbounded length executions. In particular, if there are finitely many possible system states, TLC can enumerate all of them. In practice it is possible to check billions of states, the only limit is storage (to store the BFS queue and the fingerprints) and time. In practice TLC is fast when it can use only RAM but will become extremely slow if it runs out of memory and has to store data on disk.

The disadvantage of TLC's approach is that it must enumerate states explicitly and cannot solve symbolic constraints. For example if x can feasibly take values in [1, 2^32] then TLC will have to check a state for each value. How many states will TLC have to check if (x, y) can both take values in [1, 2^32]?

## Feature asymmetry

There are features that TLC has and Apalache does't and vice versa.

[Coming soon! TODO: link to an Apalache vs TLC page with a detailed discussion]

In this tutorial we focus on Apalache, and particularly three features:

1. [The type checker](https://apalache.informal.systems/docs/apalache/typechecker-snowcat.html)\
Apalache comes with a type checker for TLA+ which helps you to develop models without creating bugs in the model itself
2. [Trace invariants](https://apalache.informal.systems/docs/apalache/principles/invariants.html?highlight=invariant#trace-invariants)\
Apalache lets you define boolean functions over the entire sequence of states in an execution. This lets you detect system behavior that single state boolean functions would not be able to detect
3. [Enumerating counterexamples](https://apalache.informal.systems/docs/apalache/principles/enumeration.html?highlight=enumer#enumerating-counterexamples)\
Apalache can generate multiple traces for a given behavior. This enables generating thorough tests for a real system.
