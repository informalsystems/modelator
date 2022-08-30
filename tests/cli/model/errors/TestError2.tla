---- MODULE TestError2 ----
\* Variable with incorrect Apalache type (should be Str).
VARIABLE
    \* @type: String;
    x
Init == x \in {"a"}
Next == UNCHANGED x
Inv == x \in {"a"}
===========================
