------------------------------ MODULE IndicesBalancesExec ------------------------------
\* This is the model of Substrate Frame Indices from 
\* https://github.com/paritytech/substrate/tree/master/frame/indices 
\* at this commit: https://git.io/Ju5Jv
\*\*
\* This is the execution environment for the Indices model.
\* This model should extend either Indices.tla or IndicesBalances.tla.
\*
\* This TLA+ model is created for demostrative purposes of MBT capabilities.
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS IndicesBalances


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
          UNCHANGED <<indices, balances>>

TransferAction ==
  \E who, new \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Transfer", who |-> who, new |-> new, index |-> index ]
    /\ LET outcome == TransferOutcome(who, new, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Transfer(who, new, index)
        ELSE
          UNCHANGED <<indices, balances>>

FreeAction ==
  \E who \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Free", who |-> who, index |-> index ]
    /\ LET outcome == FreeOutcome(who, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Free(who, index)
        ELSE
          UNCHANGED <<indices, balances>>

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
          UNCHANGED <<indices, balances>>


FreezeAction ==
  \E who \in Addresses:
  \E index \in Indices:
    /\ action' = [ type |-> "Freeze", who |-> who, index |-> index ]
    /\ LET outcome == FreezeOutcome(who, index) IN 
        actionOutcome' = outcome /\
        IF outcome = OK THEN
          Freeze(who, index)
        ELSE
          UNCHANGED <<indices, balances>>


ShashReservedAction ==
  \E who \in Addresses:
    /\ action' = [ type |-> "SlashReserved", who |-> who ]
    /\ actionOutcome' = OK
    /\ SlashReserved(who)
    /\ UNCHANGED indices


Next == 
  \/ ClaimAction
  \/ TransferAction
  \/ FreeAction
  \/ ForceTransferAction
  \/ FreezeAction
  \/ ShashReservedAction


\* Auxiliary operators

TakenIndices == { i \in DOMAIN indices : indices[i].who /= None }

=============================================================================


