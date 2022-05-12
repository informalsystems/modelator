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
        /\ y = 0
    )

Inv2 == 
    x = "hihi"


=========