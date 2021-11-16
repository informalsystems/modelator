------------------------------ MODULE IndicesHistoryTests ------------------------------
\* The Model-based tests with history tracking for Substrate Frame Indices.
\* They are meant to replace the hand-written tests from
\* https://github.com/paritytech/substrate/blob/master/frame/indices/src/tests.rs
\* at this commit: https://git.io/JzJjQ
\*
\* Please see Indices.tla for the main model.
\*
\* Run `modelator trace IndicesHistoryTests.tla Indices.cfg` for generating all tests
\* Run `modelator trace -t <TestName> IndicesHistoryTests.tla IndicesTests.cfg` for a specific test
\* Run `modelator trace -n <NumTests> IndicesHistoryTests.tla IndicesTests.cfg` for multiple tests
\* You can also combine `-t` and `-n` options.
\*
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS IndicesExec

VARIABLES 
  \* @type: Int;
  nsteps,
  \* @typeAlias: HISTORY = Int -> [action: ACTION, actionOutcome: Str];
  \* @type: HISTORY;
  history


\* This predicate extends the Init predicate with history tracking
InitForTest ==
  /\ Init
  /\ nsteps = 0
  /\ history = [ n \in {0} |->
     [ action |-> action, actionOutcome |-> actionOutcome]]

\* This predicate extends the Next predicate with history tracking
NextForTest ==
  /\ Next
  /\ nsteps' = nsteps + 1
  /\ history' = [ n \in DOMAIN history \union {nsteps'} |->
       IF n = nsteps' THEN
         [ action |-> action', actionOutcome |-> actionOutcome']
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


=============================================================================


