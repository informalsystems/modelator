---- MODULE Test2 ----
CONSTANT
    \* @type: Set(Str);
    X
VARIABLE
    \* @type: Str;
    x
Init == x \in X
Next == UNCHANGED x
Inv == x \in X
----------------------
InstanceX == {"a", "b"}
ConstInit == X = InstanceX
======================
