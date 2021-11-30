---- MODULE hello_world_typed ----

EXTENDS Sequences \* Import Sequences module from the standard library

VARIABLES
    \* @type: Set(Str);
    alices_outbox,
    \* @type: Set(Str);
    network,
    \* @type: Str;
    bobs_mood,
    \* @type: Seq(Str);
    bobs_inbox

\* @type: () => Bool;
Init ==
    /\ alices_outbox = {} \* Alice's memory of what she sent is the empty set
    /\ network = {} \* AND so is the network
    /\ bobs_mood = "neutral" \* AND Bob's mood is neutral
    /\ bobs_inbox = <<>> \* AND Bob'b inbox is an empty Sequence (list)

\* @type: (Str) => Bool;
AliceSend(m) == 
    /\ m \notin alices_outbox
    /\ alices_outbox' = alices_outbox \union {m}
    /\ network' = network \union {m}
    /\ UNCHANGED <<bobs_mood, bobs_inbox>>

\* @type: () => Bool;
NetworkLoss == 
    /\ \E e \in network: network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, bobs_inbox, alices_outbox>>

\* @type: () => Bool;
NetworkDeliver == 
    /\ \E e \in network:
        /\ bobs_inbox' = bobs_inbox \o <<e>> 
        /\ network' = network \ {e}
    /\ UNCHANGED <<bobs_mood, alices_outbox>>

\* @type: () => Bool;
BobCheckInbox == 
    /\ bobs_mood' = IF bobs_inbox = <<"hello", "world">> THEN "happy" ELSE "neutral"
    /\ UNCHANGED <<network, bobs_inbox, alices_outbox>>

\* @type: () => Bool;
Next ==
    \/ AliceSend("hello")
    \/ AliceSend("world")
    \/ NetworkLoss
    \/ NetworkDeliver
    \/ BobCheckInbox

\* @type: () => Bool;
NothingUnexpectedInNetwork == \A e \in network: e \in alices_outbox

\* @type: () => Bool;
NotBobIsHappy == 
    LET BobIsHappy == bobs_mood = "happy"
    IN ~BobIsHappy

====