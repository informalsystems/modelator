---- MODULE collatz ----
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    x

Init ==
    x \in 1..100

Next ==
    x' = IF (x % 2 = 0) THEN (x \div 2) ELSE (x * 3 + 1)

Inv ==
    x /= 1

====
