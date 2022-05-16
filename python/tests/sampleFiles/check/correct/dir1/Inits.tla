---- MODULE Inits ----

VARIABLES
    \* @type: Str;
    x,
    \* @type: Int;
    y

InitA ==
    /\ x = "hello"
    /\ y = 32

InitB ==
    /\ x = "ho"
    /\ y = 0

====
