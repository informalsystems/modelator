Syntactically invalid TLA+: there is an extra comma after the variable declaration.
---- MODULE TestError1 ----
VARIABLE x,
Init == x \in {"a"}
Next == UNCHANGED x
Inv == x \in {"a"}
===========================
