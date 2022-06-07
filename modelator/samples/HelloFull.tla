------------ MODULE HelloFull -------------

EXTENDS Naturals, FiniteSets, Sequences

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

Inv ==
    ~
    (
        /\ x = "world"
        /\ y = 20
    )

Inv2 ==
    y /= 11


ExTest ==
    y = 10



===========================================
