---- MODULE hanoi ----
EXTENDS Apalache, Integers, Sequences, SequencesExt

VARIABLES
    \* @type: Seq(Seq(Int));
    hanoi,
    \* @type: {tag: Str, source: Int, target: Int};
    action

N_DISC == 3

INIT_TOWER ==
    LET
    \* @type: (Seq(Int), Int) => Seq(Int);
    NotLambda(s,i) == <<i>> \o s
    IN ApaFoldSet(NotLambda, <<>>, 1..N_DISC)

Init ==
    /\ hanoi = << INIT_TOWER, <<>>, <<>> >>
    /\ action = [tag |-> "init", source |-> 0, target |-> 0]


\* @type: (Int, Int) => Bool;
IsValidMove(source, target) ==
    /\ Len(hanoi[source]) > 0
    /\ (Len(hanoi[target]) = 0 \/ Last(hanoi[source]) < Last(hanoi[target]))


\* @type: (Int, Int) => Seq(Seq(Int));
Move(source, target) ==
    [
        hanoi EXCEPT
        ![source] = Front(@),
        ![target] = Append(@, Last(hanoi[source]))
    ]


Next ==
    \E source \in 1..3, target \in 1..3:
        /\ source /= target
        /\ IsValidMove(source, target)
        /\ hanoi' = Move(source, target)
        /\ action' = [tag |-> "move", source |-> source, target |-> target]


Test ==
    hanoi = << <<>>, <<>>, INIT_TOWER >>

====
