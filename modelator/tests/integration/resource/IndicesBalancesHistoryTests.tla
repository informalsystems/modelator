------------------------------ MODULE IndicesHistoryTests ------------------------------
\* The Model-based tests with history tracking for Substrate Frame Indices.
\* They are meant to replace the hand-written tests from
\* https://github.com/paritytech/substrate/blob/master/frame/indices/src/tests.rs
\* at this commit: https://git.io/JzJjQ
\*
\* Please see IndicesBalances.tla for the main model.
\*
\* Run `modelator trace IndicesBalancesHistoryTests.tla Indices.cfg` for generating all tests
\* Run `modelator trace -t <TestName> IndicesBalancesHistoryTests.tla IndicesTests.cfg` for a specific test
\* Run `modelator trace -n <NumTests> IndicesBalancesHistoryTests.tla IndicesTests.cfg` for multiple tests
\* You can also combine `-t` and `-n` options.
\*
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS IndicesBalancesExec

VARIABLES 
  \* @type: Int;
  nsteps,
  \* @typeAlias: HISTORY = Int -> [action: ACTION, actionOutcome: Str, balances: BALANCES];
  \* @type: HISTORY;
  history


\* This predicate extends the Init predicate with history tracking
InitForTest ==
  /\ Init
  /\ nsteps = 0
  /\ history = [ n \in {0} |->
     [ action |-> action, actionOutcome |-> actionOutcome, balances |-> balances ]]

\* This predicate extends the Next predicate with history tracking
NextForTest ==
  /\ Next
  /\ nsteps' = nsteps + 1
  /\ history' = [ n \in DOMAIN history \union {nsteps'} |->
       IF n = nsteps' THEN
         [ action |-> action', actionOutcome |-> actionOutcome', balances |-> balances']
       ELSE history[n]
     ]

\* The view for the tests
\* @type: <<Str, Str>>;
View == << action.type, actionOutcome >>

\* The set of all actions in the history with the given type
Actions(type) ==
  { history[i]: i \in { i \in DOMAIN(history): history[i].action.type = type } }
    

Test2Steps ==
  nsteps = 2

Test3Steps ==
  nsteps = 3

Test2Claim ==
  Cardinality(Actions("Claim")) = 2

Test3Claim ==
  Cardinality(Actions("Claim")) = 3

Test2Free ==
  Cardinality(Actions("Free")) = 2

Test3Free ==
  Cardinality(Actions("Free")) = 3

Test2Freeze ==
  Cardinality(Actions("Freeze")) = 2

Test3Freeze ==
  Cardinality(Actions("Freeze")) = 3

TestIndexTakenWithoutReserveAndForceFreeze ==
  /\ \E index \in TakenIndices:
       balances[indices[index].who].reserved = 0
  /\ Actions("ForceTransfer") = {}
  /\ Actions("Freeze") = {}


TestTransferFundsViaIndices ==
  \E a1, a2 \in Addresses:
  \E s1, s2 \in DOMAIN history:
  LET S1 == history[s1] IN 
  LET S2 == history[s2] IN
    /\ S1.balances[a1].free + S1.balances[a2].free = S2.balances[a1].free + S2.balances[a2].free
    /\ S1.balances[a1].free /= S2.balances[a1].free
    /\ \A a \in Addresses:
         /\ S1.balances[a].reserved = S2.balances[a].reserved
         /\ a = a1 \/ a = a2 \/ S1.balances[a].free = S2.balances[a].free


=============================================================================
