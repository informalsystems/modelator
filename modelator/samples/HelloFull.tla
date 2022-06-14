------------ MODULE HelloFull -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Int;
    x,
    \* @type: Str;
    y

Init ==
    /\ x = 1400
    /\ y = "hello"

Next ==
    /\ x' = x-2
    /\ y' = "world"


Inv ==
    x /= 1396

AlwaysEvenInvariant ==
    x % 2 = 0



ExTest ==
    x = 1394



===========================================
