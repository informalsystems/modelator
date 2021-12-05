---
title: Typechecking
description: How to type check your models
layout: default
parent: TLA+ Basics Tutorials
nav_order: 4
---

# Typechecking

**The .tla and other referenced files are included [here](https://github.com/informalsystems/modelator/tree/main/jekyll/docs/tla_basics_tutorials/models).**

As a model grows it becomes difficult to ensure that the TLA+ code in the models is doing what you think it is. There are techniques to help ensure there are no bugs in your model. The best way to make sure your model is high quality is to use types and the Apalache type checker.

Apalache comes with a type checker. The [docs](https://apalache.informal.systems/docs/HOWTOs/howto-write-type-annotations.html) contain all the details. In this tutorial we will type the model of Alice and Bob's interactions in hello_world.tla. We will use a subset of the built in types. The full list of builtin types can be found [here](https://apalache.informal.systems/docs/adr/002adr-types.html?highlight=types#11-type-grammar-type-system-1-or-ts1).


## Typechecking

Our model of Alice and Bob's interaction is simple: the state variables are simple data structures.

We should type the variables with a particular data structure.

```tla
VARIABLES
    \* @type: Set(Str);
    alices_outbox,
    \* @type: Set(Str);
    network,
    \* @type: Str;
    bobs_mood,
    \* @type: Seq(Str);
    bobs_inbox
```

The Apalache type system works by annotating lines of code with special TLA+ comments

```
\* @type: ...
```

We have specified that 

1. _alices_outbox_ is a set of strings
2. _network_ is a set of strings
3. _bobs_mood_ is a string
4. _bobs_inbox_ is a sequence of strings

We can also specify the type of operators. For example we can annotate AliceSend(m)

```tla
\* @type: (Str) => Bool;
AliceSend(m) == 
    /\ m \notin alices_outbox
    /\ alices_outbox' = alices_outbox \union {m}
    /\ network' = network \union {m}
    /\ UNCHANGED <<bobs_mood, bobs_inbox>
```

The annotation says that AliceSend is an operator taking strings and returning booleans.
(Note that very often the typechecker can infer annotations for operators automatically. It is able to do so for the operator AliceSend, too. You can try typechecking with the manual annotation left out.)

Finally we can typecheck the model

```bash
java -jar apalache-pkg-0.17.5-full.jar typecheck hello_world_typed.tla

# Apalache output:
# ...
# Type checker [OK]
```
