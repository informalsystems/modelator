---
title: Advanced cheat sheet
description: Advanced cheatsheet
layout: default
parent: Tla+
grand_parent: Model Based Testing
---
# TLA+ Advanced Cheatsheet

This cheatsheet contains some additional syntactic sugar, and uses the official TLA+ terminology in the descriptions.

```
a /= b                      \* a not equals b
a # b                       \* a not equals b
~a                          \* not a
/\                          \* and
\/                          \* or
S \cup T                    \* S union T
S \cap T                    \* S intersect T
S \union T                  \* S union T
S \intersect T              \* S intersect T
S \ T                       \* S less T
\A x \in S:                 \* for all elements x in the set S ..
\E x \in S:                 \* there exists x in the set S such that ..
{a,b,c}                     \* the set containing a,b,c
{x \in S: P(x)}             \* the set of elements in S such that P(x)
\SUBSET S                   \* the powerset of S (set of all subsets)
\UNION S                    \* the union of all sets in S (S is a set of sets)
f[e]                        \* the value of f at e
DOMAIN f                    \* the domain of the function f
[x \in S |-> g(x)]          \* the function mapping elements x in S to the value of g(x)
[S -> T]                    \* the set of functions mapping values in the set S to values in the set T
[f EXCEPT ![x] = y]         \* the function f, except for x is remapped to y
[f EXCEPT ![x] = g(@)]      \* the function f, except for x is remapped to the value of g(f[x])
f.x                         \* the value of x in the record f
[k1 |-> v1, k2 |-> v2, ...] \* the record where keys are the strings k1, k2.. mapped to
                            \* their respective values
[k1 : V1, k2 : V2, ...]     \* the set of records mapping strings k1, k2.. to elements
                            \* in their respective sets 
[f EXCEPT !.x = y]          \* the record f, except for x is remapped to y (but x must be a string)
[f EXCEPT !.x = g(@)]       \* the record f, except for x is remapped to g(f.x) (but x must be a string)
t[i]                        \* the ith element of the sequence t (1-indexed!)
a \o b                      \* the sequences a and b concatenated
<<a,b,c>>                   \* explicit sequence
S \X T \X .. \X SN        \* the set of length N sequences with ith elements in Si
IF P THEN x ELSE y          \* if/else

CASE                        \* case switch
       pred1 -> g1()
    [] pred2 -> g2()
    [] pred3 -> g3()
    ...
    [] OTHER -> gN()
    
f @@ g                      \* the merger of functions f and g, with f taking higher priority
a :> b                      \* the function with only the value a mapping to value b
x \in Int                   \* an integer x
Len(v)                      \* the length of the sequence v
Append(v, e)                \* the sequence v with e added to the end
Head(v)                     \* the first element of the sequence v
SubSeq(v, i, j)             \* the subsequence of v from indexes i..j inclusive
```
