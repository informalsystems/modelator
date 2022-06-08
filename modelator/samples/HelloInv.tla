------------ MODULE HelloInv -------------
VARIABLES
    \* @type: Str;
    x,
    \* @type: Str;
    y


Inv ==
    ~
    (
        /\ x = "world"
        /\ y = 20
    )

Inv2 ==
    y = 10


=========
