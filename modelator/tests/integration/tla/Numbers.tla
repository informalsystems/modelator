------------------------------- MODULE Numbers ------------------------------
EXTENDS Integers
-----------------------------------------------------------------------------

CONSTANT MaxNumber

VARIABLE a, b

Init ==
    /\ a = 0
    /\ b = 0

IncreaseA ==
    LET nextA == a + 1 IN
    IF nextA <= MaxNumber THEN
        /\ a' = nextA
        /\ UNCHANGED <<b>>
    ELSE
        /\ UNCHANGED <<a, b>>

IncreaseB ==
    LET nextB == b + 2 IN
    IF nextB <= MaxNumber THEN
        /\ b' = nextB
        /\ UNCHANGED <<a>>
    ELSE
        /\ UNCHANGED <<a, b>>

Next ==
    \/ IncreaseA
    \/ IncreaseB
    \/ UNCHANGED <<a, b>>

TypeOK ==
    /\ a \in Int
    /\ b \in Int

Inv ==
    /\ a <= MaxNumber
    /\ b <= MaxNumber

============================================================================
