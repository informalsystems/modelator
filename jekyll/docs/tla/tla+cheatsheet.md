---
title: Cheatsheet
layout: default
parent: Tla+
grand_parent: Model Based Testing
---
# TLA+ Cheatsheet

## TLA+ Quick Start - contains enough to model almost anything

```tla
(* Comments *)

(* This is 
   multiline comment *)
\* This is single line comment

(* Module structure *)

---- MODULE example ----    \* Starts TLA+ module (should be in file example.tla)
====                        \* Ends TLA+ module (everything after that is ignored)

VARIABLES x, y, ...         \* declares variables x, y, ...
CONSTANTS x, y, ...         \* declares constants x, y, ... (should be defined in configuration)

Name == e                   \* defines operator Name without parameters, and with expression e as a body
Name(x, y, ...) == e        \* defines operator Name with parameters x, y, ..., and body e (may refer to x, y, ...)

(* Boolean logic *)

TRUE                        \* Boolean true
FALSE                       \* Boolean false
~x                          \* not x; negation
x /\ y                      \* x and y; conjunction (can be also put at line start, in multi-line conjunctions)
x \/ y                      \* x or y; disjunction (can be also put at line start, in multi-line disjunctions)
x = y                       \* x equals y
x /= y                      \* x not equals y
x => y                      \* implication: y is true whenever x is true
x <=> y                     \* equivalence: x is true if and only if y is true

(* Integers *)              \* EXTENDS Integers (should extend standard module Integers)

1, -2, 1234567890           \* integer literals; integers are unbounded
a..b                        \* integer range: all integers between a and b inclusive
-x                          \* integer negation: negate the integer literal or variable x
x + y, x - y, x * y         \* integer addition, subtraction, multiplication
x < y, x <= y               \* less than, less than or equal
x > y, x >= y               \* greater than, greater than or equal

(* Finite sets *)           \* EXTENDS FiniteSets (should extend standard module FiniteSets)

{a, b, c}                 \* set constructor: the set containing a, b, c
Cardinality(S)              \* number of elements in set S
x \in S                     \* x belongs to set S
x \notin S                  \* x does not belong to set S
S \subseteq T               \* is set S a subset of set T? true of all elements of S belong to T
S \union T                  \* union of sets S and T: all x belonging to S or T
S \intersect T              \* intersection of sets S and T: all x belonging to S and T
S \ T                       \* set difference, S less T: all x belonging to S but not T
{x \in S: P(x)}             \* set filter: selects all elements x in S such that P(x) is true
{e: x \in S}                \* set map: maps all elements x in set S to expression e (which may contain x)

(* Quantifiers *)

\A x \in S:                 \* for all elements x in set S it holds that ..
\E x \in S:                 \* there exists an element x in set S such that ..

(* Functions *) 

[x \in S |-> e]             \* function constructor: maps all keys x from domain S to expression e (may refer to x) 
f[x]                        \* function application: the value of function f at key x
DOMAIN f                    \* function domain: the set of keys of function f
[f EXCEPT ![x] = e]         \* function f with key x remapped to expression e (may reference @, the original f[x])
[f EXCEPT ![x] = e1,        \* function f with multiple keys remapped: 
          ![y] = e2, ...]   \*   x to e1 (@ in e1 will be equal to f[x]), y to e2 (@ in e2 will be equal to f[y])

(* Records *)

[x |-> e1, y |-> e2, ...]   \* record constructor: a record equal at field x to e1, and at y to e2 
r.x                         \* record field access: the value of field x of record r
[r EXCEPT !.x = e]          \* record r with field x remapped to expression e (may reference @, the original r.x)
[r EXCEPT !.x = e1,         \* record r with multiple fields remapped: 
          !.y = e2, ...]    \*   x to e1 (@ in e1 is equal to r.x), y to e2 (@ in e2 is equal to r.y)

(* Sequences *)             \* EXTEND Sequences (should extend standard module Sequences)

<<a,b,c>>                   \* sequence constructor: a sequence containing elements a, b, c
s[i]                        \* the ith element of the sequence t (1-indexed!)
s \o t                      \* the sequences s and t concatenated
Len(s)                      \* the length of sequence s
Append(s, x)                \* the sequence s with x added to the end
Head(s)                     \* the first element of sequence s

(* Control structures *)

IF P THEN x ELSE y          \* if P is true, then x should be true; otherwise y should be true
```

## Apalache

```
\* A handy alias for calling Apalache
alias apalache="java -jar apalache-pkg-0.17.5-full.jar --nworkers=8"

\* Typecheck
apalache typecheck <.tla file>

\* Model check assuming a .cfg file with the same name as the .tla file is present
apalache check <.tla file>

\* Model check assuming with a specific .cfg file
apalache check --config=<.cfg file> <.tla file>

\* TODO:
apalache check --view=<View Operator Name> <.tla file>

```


## TLC

```
\* A handy alias providing the JVM with 12GB of RAM (adjust accordingly) and using multiple threads
alias tlc="java -XX:+UseParallelGC -Xmx12g -cp tla2tools.jar tlc2.TLC -workers auto" 

\* Model check with TLC
tlc -config <.config file> <.tla file> 

\* Run TLC in simulation mode
tlc -config <.config file> -simulate <.tla file>
```
