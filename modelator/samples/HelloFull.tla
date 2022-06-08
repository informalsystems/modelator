------------ MODULE HelloFull -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Str;
    x,
    \* @type: Int;
    y

Init ==
    /\ x = "hello"
    /\ y = 8400

Next ==
    /\ x' = IF x = "hello" THEN  "world" ELSE "hello"
    /\ y' = y-2

\* Inv ==
\*     ~
\*     (
\*         /\ x = "world"
\*         /\ y = 20
\*     )

Inv == y /= 8396
Inv2 == y /= 8394
\* Inv2 ==
\*     y /= 11

Inv3 ==
    y /= 4398

Inv4 ==
    y /= 160


ExTest ==
    y = 10



===========================================
