----- MODULE HourClock -----

EXTENDS Naturals, Sequences
VARIABLES 
  \* @typeAlias: STATE = [ hr: Int ];
  \* @type: Int;
  hr
Init == hr \in (1..12)
Next == hr' = IF hr /= 12 THEN hr + 1 ELSE 1

============================