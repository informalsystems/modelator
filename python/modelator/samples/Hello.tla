------------ MODULE Hello -------------

EXTENDS Naturals, FiniteSets, Sequences, HelloInv

VARIABLES
    \* @type: Str;
    x,
    \* @type: Int;
    y

Init ==
    /\ x = "hello"
    /\ y = 22

Next ==
    /\ x' = IF x = "hello" THEN  "world" ELSE "hello"
    /\ y' = y-2



===========================================
