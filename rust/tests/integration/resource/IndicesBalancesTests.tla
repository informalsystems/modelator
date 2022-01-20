------------------------------ MODULE IndicesBalancesTests ------------------------------
\* The Model-based tests for Substrate Frame Indices.
\* They are meant to replace the hand-written tests from
\* https://github.com/paritytech/substrate/blob/master/frame/indices/src/tests.rs
\* at this commit: https://git.io/JzJjQ
\*
\* Please see IndicesBalances.tla for the main model,
\* and IndicesBalancesExec.tla for the execution environment (actions).
\*
\* Run `modelator trace IndicesBalances.tla Indices.cfg` for generating all tests
\* Run `modelator trace -t <TestName> IndicesBalances.tla IndicesTests.cfg` for a specific test
\* Run `modelator trace -n <NumTests> IndicesBalances.tla IndicesTests.cfg` for multiple tests
\* You can also combine `-t` and `-n` options.
\*
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS IndicesBalancesExec

\* The view for the tests
\* @type: <<Str, Str>>;
View == << action.type, actionOutcome >>

InitForTest == Init
NextForTest == Next

TestClaim == 
  action.type = "Claim"

TestFree == 
  action.type = "Free"

TestFreeze == 
  action.type = "Freeze"

TestFreezeSuccess ==
  /\ action.type = "Freeze"
  /\ actionOutcome = "OK"

Test3Taken ==
  Cardinality(TakenIndices) >= 3

TestIndexTakenWithoutReserve ==
  \E index \in TakenIndices:
    balances[indices[index].who].reserved = 0

TestIndexTakenWithoutReserveAndForce ==
  /\ action.type /= "ForceTransfer"
  /\ \E index \in TakenIndices:
       balances[indices[index].who].reserved = 0


=============================================================================


