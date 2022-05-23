------------ MODULE Hello -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Str;
    x,
    \* @type: Int;
    y

InitA ==
    /\ x = "hello"
    /\ y = 42

InitB ==
    /\ x = "hi"
    /\ y = 42

InitC ==
    /\ x = "hello"
    /\ y = 0

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
