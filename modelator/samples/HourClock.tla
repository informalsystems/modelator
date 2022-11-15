----- MODULE HourClock -----

EXTENDS Naturals, Sequences
VARIABLES
  \* @typeAlias: state = { hr: Int };
  \* @type: Int;
  hr
Init == hr \in (1..12)
Next == hr' = IF hr /= 12 THEN hr + 1 ELSE 1

============================
