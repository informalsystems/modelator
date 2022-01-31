------------------------------ MODULE IndicesExec ------------------------------
\* This is the model of Substrate Frame Indices from 
\* https://github.com/paritytech/substrate/tree/master/frame/indices 
\* at this commit: https://git.io/Ju5Jv
\*\*
\* This is the execution environment for the Indices.tla model.
\*
\* This TLA+ model is created for demostrative purposes of MBT capabilities.
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS Indices


\* Actions: boilerplate code that checks preconditions, executes updates,
\* and stores action and actionOutcome.
\* This code will be auto-generated in the next versions of Modelator.

ClaimAction ==
  \E who \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Claim", who |-> who, index |-> index ]
    /\ LET outcome == ClaimOutcome(who, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Claim(who, index)
        ELSE
          UNCHANGED <<indices, reserved>>

TransferAction ==
  \E who, new \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Transfer", who |-> who, new |-> new, index |-> index ]
    /\ LET outcome == TransferOutcome(who, new, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Transfer(who, new, index)
        ELSE
          UNCHANGED <<indices, reserved>>

FreeAction ==
  \E who \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Free", who |-> who, index |-> index ]
    /\ LET outcome == FreeOutcome(who, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Free(who, index)
        ELSE
          UNCHANGED <<indices, reserved>>

ForceTransferAction ==
  \E who, new \in Addresses:
  \E index \in Indices:
  \E freeze \in BOOLEAN:
    /\ action' = [ type |-> "ForceTransfer", who |-> who, new |-> new, index |-> index, freeze |-> freeze ]
    /\ LET outcome == ForceTransferOutcome(who, new, index, freeze) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          ForceTransfer(who, new, index, freeze)
        ELSE
          UNCHANGED <<indices, reserved>>


FreezeAction ==
  \E who \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Freeze", who |-> who, index |-> index ]
    /\ LET outcome == FreezeOutcome(who, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Freeze(who, index)
        ELSE
          UNCHANGED <<indices, reserved>>


Next == 
  \/ ClaimAction
  \/ TransferAction
  \/ FreeAction
  \/ ForceTransferAction
  \/ FreezeAction


\* Auxiliary operators

TakenIndices == { i \in DOMAIN indices : indices[i].who /= None }

\* Is it an invariant?

IndexRequiresReserve ==
  \A index \in TakenIndices:
    reserved[indices[index].who] /= 0


\* Negate the above to get the test
TestIndexWithoutReserve ==
  \E index \in TakenIndices:
    reserved[indices[index].who] = 0

=============================================================================


