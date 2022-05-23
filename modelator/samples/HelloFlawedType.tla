------------ MODULE HelloFlawedType -------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLES
    \* @type: Str;
    x,
    \* @type: Str;
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
