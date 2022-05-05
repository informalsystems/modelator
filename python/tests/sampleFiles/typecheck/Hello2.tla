------------ MODULE Hello2 -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Str;
    x,    
    y

Init ==
    /\ x = "hello"
    /\ y = 42

Next ==
    /\ x' = IF x = "hello" THEN "world" ELSE "hello"
    /\ y' = 42-y

Inv ==
    ~
    (
        /\ x = "world"
        /\ y = 0
    )


===========================================