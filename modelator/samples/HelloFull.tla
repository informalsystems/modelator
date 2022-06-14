------------ MODULE HelloFull -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Str;
    x,
    \* @type: Int;
    y

Init ==
    /\ x = "hello"
    /\ y = 1400

Next ==
    /\ x' = IF x = "hello" THEN  "world" ELSE "hello"
    /\ y' = y-2


Inv == y /= 1396


AlwaysEven ==
    y % 2 = 0



ExTest ==
    y = 1394



===========================================
