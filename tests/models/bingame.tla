---- MODULE bingame ----
EXTENDS Integers

VARIABLES
    \* @type: Int;
    number,
    \* @type: Str;
    action


Init ==
    /\ number = 0
    /\ action = "Zero"

Next ==
    /\ action' \in {"AddOne", "MultiplyTwo"}
    /\ number' =
        IF action' = "AddOne" THEN number + 1 ELSE
        IF action' = "MultiplyTwo" THEN number * 2 ELSE
        -1

Inv ==
    number /= 30

====
