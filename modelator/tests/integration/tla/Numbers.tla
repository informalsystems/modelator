------------------------------- MODULE Numbers ------------------------------
EXTENDS Integers
-----------------------------------------------------------------------------

CONSTANT MaxNumber

VARIABLE a, b, action

Init ==
    /\ a = 0
    /\ b = 0
    /\ action = ""

IncreaseA ==
    LET nextA == a + 1 IN
    IF nextA <= MaxNumber THEN
        /\ a' = nextA
        /\ action' = "IncreaseA"
        /\ UNCHANGED <<b>>
    ELSE
        /\ UNCHANGED <<a, b, action>>

IncreaseB ==
    LET nextB == b + 2 IN
    IF nextB <= MaxNumber THEN
        /\ b' = nextB
        /\ action' = "IncreaseB"
        /\ UNCHANGED <<a>>
    ELSE
        /\ UNCHANGED <<a, b, action>>

Next ==
    \/ IncreaseA
    \/ IncreaseB
    \/ UNCHANGED <<a, b, action>>

TypeOK ==
    /\ a \in Int
    /\ b \in Int

Inv ==
    /\ a <= MaxNumber
    /\ b <= MaxNumber

============================================================================
