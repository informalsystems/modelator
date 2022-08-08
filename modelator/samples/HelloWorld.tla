----- MODULE HelloWorld -----

EXTENDS Naturals
CONSTANTS
  \* @type: Int;
  MAX
VARIABLES
  \* @type: Int;
  x
Init == x = 0
Next == x <= MAX /\ x' = x + 1
Inv  == x >= 0 /\ x<= MAX

=============================
