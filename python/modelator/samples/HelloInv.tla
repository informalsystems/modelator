------------ MODULE HelloInv -------------
VARIABLES
    \* @type: Str;
    x,
    \* @type: Int;
    y


Inv ==
    ~
    (
        /\ x = "world"
        /\ y = 20
    )

Inv2 ==
    y /= 10


=========
