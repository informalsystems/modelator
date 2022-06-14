------------ MODULE HelloFull -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Int;
    x

Init ==
    x = 1400

Next ==
    x' = x-2


Inv ==
    x /= 1396


AlwaysEven ==
    x % 2 = 0



ExTest ==
    x = 1394



===========================================
