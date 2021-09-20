------------------------------ MODULE IndicesTests ------------------------------
\* The Model-based tests for Substrate Frame Indices.
\* They are meant to replace the hand-written tests from
\* https://github.com/paritytech/substrate/blob/master/frame/indices/src/tests.rs
\* at this commit: https://git.io/JzJjQ
\*
\* Please see Indices.tla for the main model,
\* and IndicesExec.tla for the execution environment (actions).
\*
\* Run `modelator trace IndicesTests.tla Indices.cfg` for generating all tests
\* Run `modelator trace -t <TestName> IndicesTests.tla Indices.cfg` for a specific test
\* Run `modelator trace -n <NumTests> IndicesTests.tla Indices.cfg` for multiple tests
\* You can also combine `-t` and `-n` options.
\*
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS IndicesExec

\* The view for the tests
\* @type: <<Str, Str>>;
View == << action.type, actionOutcome >>

TestInit == Init
TestNext == Next

TestClaim == 
  action.type = "Claim"

TestFree == 
  action.type = "Free"

TestFreeze == 
  action.type = "Freeze"


Test2Steps ==
  nsteps = 2

TestFreezeSuccess ==
  /\ action.type = "Freeze"
  /\ actionOutcome = "OK"

Test3Taken ==
  Cardinality(TakenIndices) >= 3

TestIndexTakenWithoutReserve ==
  \E index \in TakenIndices:
    reserved[indices[index].who] = 0

=============================================================================


