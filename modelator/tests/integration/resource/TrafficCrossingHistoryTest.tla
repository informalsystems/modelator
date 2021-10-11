---- MODULE TrafficCrossingHistoryTest ----

\* Here we manually introduce the history variable 

EXTENDS TrafficCrossing

VARIABLES 
  \* @type: Int;
  nsteps,
  \* @type: Int -> [lights: LIGTHS, cars: CARS];
  history

\* This predicate extends the Init predicate with history tracking
InitHistory ==
  /\ DefaultInit
  /\ nsteps = 0
  /\ history = [ n \in {0} |->
     [ lights |-> lights, cars |-> cars]]

\* This predicate extends the Next predicate with history tracking
NextHistory ==
  /\ DefaultNext
  /\ nsteps' = nsteps + 1
  /\ history' = [ n \in DOMAIN history \union {nsteps'} |->
       IF n = nsteps' THEN
         [ lights |-> lights', cars |-> cars']
       ELSE history[n]
     ]


TestTwoGreens == 
  \E s1, s2 \in DOMAIN history: 
    /\ s1 /= s2
    /\ \A s \in {s1, s2}:
       \E r \in DOMAIN history[s].lights : history[s].lights[r] = "green"

TestTwoYellow == 
  \E s1, s2 \in DOMAIN history: 
    /\ s1 /= s2
    /\ \A s \in {s1, s2}:
       \E r \in DOMAIN history[s].lights : history[s].lights[r] = "yellow"

TestTwoCarsCross == 
  \E s1, s2 \in DOMAIN history: 
    /\ s1 /= s2
    /\ \A s \in {s1, s2}:
       \E c \in DOMAIN history[s].cars : history[s].cars[c].pos = 0


=============================================================================
