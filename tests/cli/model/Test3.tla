---- MODULE Test3 ----
EXTENDS Integers
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == x' = x + 1
Inv == x \in Nat
Inv2 == x' > x
ThreeSteps == x = 3
======================
