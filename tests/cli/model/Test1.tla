---- MODULE Test1 ----
VARIABLE
    \* @type: Str;
    x
Init == x = "a"
InitB == x = "b"
Next == UNCHANGED x
Inv == x = "a"
InvB == x = "b"
======================
