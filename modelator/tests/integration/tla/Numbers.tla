------------------------------- MODULE Numbers ------------------------------
EXTENDS Integers
-----------------------------------------------------------------------------

CONSTANT MaxNumber

VARIABLE a, b, action, actionOutcome

Init ==
    /\ a = 0
    /\ b = 0
    /\ action = "None"
    /\ actionOutcome = "OK"

IncreaseA ==
    action' = "IncreaseA" /\
    LET nextA == a + 1 IN
    IF nextA <= MaxNumber THEN
        /\ a' = nextA
        /\ actionOutcome' = "OK"
        /\ UNCHANGED <<b>>
    ELSE
        /\ UNCHANGED <<a, b, action>>
        /\ actionOutcome' = "FAIL"

IncreaseB ==
    action' = "IncreaseB" /\
    LET nextB == b + 2 IN
    IF nextB <= MaxNumber THEN
        /\ b' = nextB
        /\ actionOutcome' = "OK"
        /\ UNCHANGED <<a>>
    ELSE
        /\ UNCHANGED <<a, b, action>>
        /\ actionOutcome' = "FAIL"

Next ==
    \/ IncreaseA
    \/ IncreaseB
    \/ /\ action' = "None"
       /\ actionOutcome' = "OK"
       /\ UNCHANGED <<a, b>>

TypeOK ==
    /\ a \in Int
    /\ b \in Int
    /\ action \in STRING
    /\ actionOutcome \in STRING

Inv ==
    /\ a <= MaxNumber
    /\ b <= MaxNumber

============================================================================
