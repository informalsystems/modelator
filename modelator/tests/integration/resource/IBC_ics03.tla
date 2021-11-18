------------------------------- MODULE IBC_ics03 ----------------------------------
\* This is a simplified model of IBC ICS02 from 
\* https://github.com/informalsystems/ibc-rs/tree/v0.7.0/modules/tests/support/model_based
\*
\* This file contains protocol-specific methods for ICS03 (Connection).
\* For IBC constants and state variables see IBC_state.tla.
\* For execution environment (Init & Next), invariants, and tests see IBC_tests.tla.

\* For each protocol method there is:
\*  - Method operator, that "implements" the method state updates, 
\*    assuming the preconditions for it hold;
\*  - MethodOutcome operator checks for the method preconditions, and returns 
\*    Success if all preconditions are met, or the error description if not;
\*  - MethodAction operator that surrounds method's state updates with the logic
\*    that checks preconditions, and stores method arguments and outcome
\*    in the "action" and "actionOutcome" variables.
\*
\* 2021 Andrey Kuprianov, Informal Systems


EXTENDS IBC_state


\* Possible ICS02 error outcomes
Ics02ChainNotFound == "Ics02ChainNotFound"
Ics02ClientExists == "Ics02ClientExists"
Ics02MaxClientsReached == "Ics02MaxClientsReached"
Ics02ClientNotFound == "Ics02ClientNotFound"
Ics02HeaderVerificationFailure == "Ics02HeaderVerificationFailure"


\***************************************************************
\* Protocol methods and their preconditions (expected outcomes)
\***************************************************************

\* @type: (CHAIN_ID, HEIGHT) => Str;
CreateClientOutcome(chainId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN Ics02ChainNotFound
  ELSE IF chains[chainId].clientIdCounter \in DOMAIN chains[chainId].clients
    THEN Ics02ClientExists
  ELSE IF chains[chainId].clientIdCounter >= MaxClientsPerChain 
    THEN Ics02MaxClientsReached
  ELSE Success

\* @type: (CHAIN_ID, HEIGHT) => Bool;
CreateClient(chainId, height) ==
  LET clientId == chains[chainId].clientIdCounter IN
  chains' = [chains EXCEPT 
    ![chainId] = [@ EXCEPT 
      !.height = [@ EXCEPT !.revision_height = @+1], 
      !.clientIdCounter = @+1,
      !.clients = [ c \in DOMAIN @ \union {clientId} |-> 
        IF c = clientId THEN [heights |-> {height}] ELSE @[c]]
    ]
  ]


\* @type: (CHAIN_ID, CLIENT_ID, HEIGHT) => Str;
UpdateClientOutcome(chainId, clientId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN Ics02ChainNotFound
  ELSE IF clientId \notin DOMAIN chains[chainId].clients
    THEN Ics02ClientNotFound
  ELSE IF ~HigherRevisionHeight(height, MaxHeight(chains[chainId].clients[clientId].heights))
    THEN Ics02HeaderVerificationFailure
  ELSE Success

\* @type: (CHAIN_ID, CLIENT_ID, HEIGHT) => Bool;
UpdateClient(chainId, clientId, height) ==
  chains' = [chains EXCEPT 
    ![chainId] = [@ EXCEPT 
      !.height = [@ EXCEPT !.revision_height = @+1], 
      !.clients = [@ EXCEPT 
        ![clientId] = [heights |-> @.heights \union {height}]
      ]
    ]
  ]

\******************************************************************************
\* Protocol actions: protocol methods with existentially quantified parameters
\* An action is a component of the Next relation, 
\* that checks precondition, executes update, and stores action/actionOutcome
\******************************************************************************


CreateClientAction ==
  \E chainId \in ChainIds:
  \E height \in Heights:
    /\ action' = [ type |-> "CreateClient", chainId |-> chainId, height |-> height ]
    /\ LET outcome == CreateClientOutcome(chainId, height) IN 
        actionOutcome' = outcome /\
        IF outcome = Success THEN
          CreateClient(chainId, height)
        ELSE
          UNCHANGED chains

UpdateClientAction ==
  \E chainId \in ChainIds:
  \E clientId \in ClientIds:
  \E height \in Heights:
    /\ action' = [ type |-> "UpdateClient", chainId |-> chainId, clientId |-> clientId, height |-> height ]
    /\ LET outcome == UpdateClientOutcome(chainId, clientId, height) IN 
        actionOutcome' = outcome /\
        IF outcome = Success THEN
          UpdateClient(chainId, clientId, height)
        ELSE
          UNCHANGED chains

Ics02Next ==
  \/ CreateClientAction
  \/ UpdateClientAction

===============================================================================
