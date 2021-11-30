---
title: Tutorials
description: How to make them most of the tutorials
layout: default
parent: TLA+
nav_order: 2
---

# TLA+ Basics Tutorial

This is a straightforward introduction to TLA+. By the end you should be able to write your own models of distributed systems and concurrent algorithms. You should also be able to check properties of the models, and generate execution traces which can be used in automatic testing pipelines. The target audience is software engineers who are fluent in a mainstream programming language and understand computer science.

This document contains prose. The [cheatsheet](./cheatsheet) is useful as a reference.

## TLA+ capabilities

TLA+ is a language for writing models of distributed systems and concurrent algorithms. It doesn't execute on your machine like a typical programming language: you run it through a model checker. A model checker is a program that explores all possible executions of a system. You can specify properties and behaviors, and the model checker will tell you if they hold or not. The model checker can also give you examples of behaviors.

TLA+ has been used to model a wide variety of things including [locks and allocators in the linux kernel](https://git.kernel.org/pub/scm/linux/kernel/git/cmarinas/kernel-tla.git/), the [Docker SwarmKit container orchestrator](https://github.com/docker/swarmkit/tree/master/design/tla), [Paxos consensus](https://github.com/tlaplus/DrTLAPlus/blob/master/Paxos/Paxos.tla), the [Raft replicated state machine](https://github.com/ongardie/raft.tla/blob/master/raft.tla) and more.

All TLA+ models are structured as a state machine. You specify an initial state and a collection of transitions. Additionally you can specify boolean functions (invariants) over the state. The model checker will check for boolean function violations.

To give examples: you could model a concurrent garbage collector algorithm and check that no memory leak is possible. You could also model the API for a financial transfers system, and check that it is not possible to steal funds.

## Getting set up

For these tutorials we require the TLC and Apalache model checkers.

TLC can be downloaded with

```
tlaurl=https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar;
curl -LO $tlaurl;
```

Apalache can be downloaded with 

```
apalacheurl=https://github.com/informalsystems/apalache/releases/download/v0.17.5/apalache-v0.17.5.zip;
curl -LO $apalacheurl;
```

You will need to unzip Apalache and move the jar from `mod-distribution/target/apalache-pkg-0.17.5-full.jar` to your working directory.

We recommend using the Visual Studio Code [TLA+ extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) to work on your models. It provides syntax highlighting, parsing and model checking through TLC. Model checking, parsing and other features are accessed through the VSCode context menu (cmd + shift + p on OSX).

There are more resources that we won't in this set of tutorials but that might be useful to know about. Please see [The TLA+ ecosystem](./ecosystem).

## Let's get started

We have 5 mini tutorials giving you increasing power.

1. ['Hello world' using TLC](./hello_world)
2. [Typechecking your models](./typechecking)
3. [Apalache vs TLC](./apalache_vs_tlc)
4. [Finding an Ethereum exploit using Apalache](./ethereum)
5. [Generating traces for automated testing using Apalache](./generating_traces)

That's it for the basic tutorials; congratulations!

These tutorials make up the basics of using TLA+, please see [advanced tutorials](TODO: link)!

## Footnote: what the tutorials do not include

TLA+ and its tools includes many features. We ignored the following in these basic tutorials

1. Formal proof using [TLAPS](https://apalache.informal.systems/docs/apalache/theory.html)
2. [Inductive invariants](https://apalache.informal.systems/docs/apalache/running.html?highlight=inductive#checking-an-inductive-invariant) using Apalache
3. Verifying temporal (liveness) properties [[1](https://pron.github.io/posts/tlaplus_part3), [2](https://learntla.com/temporal-logic/usage/)]
4. TLC's [symmetry sets and model values](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html)
5. Apalache's [uninterpreted types](https://apalache.informal.systems/docs/HOWTOs/uninterpretedTypes.html)

These features are useful in some circumstances. We may add sections in the future.
