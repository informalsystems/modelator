---- MODULE TrafficCrossingTest ----

EXTENDS TrafficCrossing

TestYellow == \E road \in Roads : lights[road] = "yellow"
TestRedYellow == \E road \in Roads : lights[road] = "redyellow"

TestCarCrosses == \E c \in Cars : cars[c].pos = 0

=============================================================================
