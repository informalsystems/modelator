---- MODULE multiple_traces ----

EXTENDS Integers, Sequences, Apalache, typedefs

VARIABLES
    \* @type: Str;
    auxiliary_str,
    \* @type: Int;
    important_int

Init ==
    /\ auxiliary_str = "foo"
    /\ important_int = 0

ChangeAuxiliaryStr == 
    /\ auxiliary_str' \in {"foo", "bar", "wiz"}
    /\ UNCHANGED important_int
        
AddToImportantInt == 
    /\ UNCHANGED auxiliary_str
    /\ \E x \in 1..4 : important_int' = important_int + x

Next ==
    \/ ChangeAuxiliaryStr
    \/ AddToImportantInt

\* @type: () => Bool;
ImportantIntIs6 == 
    LET Behavior == important_int = 6
    IN ~Behavior

\* @type: Seq(STATE) => Bool;
ImportantIntIsOddUntil6(trace) ==
    LET Behavior ==
        /\ trace[Len(trace)].important_int = 6
        /\ \A i \in DOMAIN trace : 
            \/ (i = 1 \/ i = Len(trace))
            \/ trace[i].important_int % 2 = 1
    IN ~Behavior

View == important_int

====