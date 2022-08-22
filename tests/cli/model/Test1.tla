---- MODULE Test1 ----
VARIABLE
    \* @type: Str;
    x
Init == x = "a"
Next == UNCHANGED x
Inv == x = "a"
Inv2 == x # "b"
======================
