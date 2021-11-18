------------------------------- MODULE IBC_0 ----------------------------------
\* A simplified IBC model from 
\* https://github.com/informalsystems/ibc-rs/tree/v0.7.0/modules/tests/support/model_based
\* originally constructed by Vitor Enes, with additions by Jehan Tremback & Andrey Kuprianov
\*
\* This is version 0, which differs from the original in these aspects:
\* - The logic of precondition checking and updates is simplified & condensed,
\*   with clear separation between the two. For each protocol `Method` there is:
\*   - `Method` operator, that "implements" the method state updates, 
\*     assuming the preconditions for it hold;
\*   - `MethodOutcome` operator checks for the method preconditions, and returns 
\*     Success if all preconditions are met, or the error description if not;
\*   - `MethodAction` operator that surrounds method's state updates with the logic
\*     that checks preconditions, and stores method arguments and outcome
\*     in the "action" and "actionOutcome" variables.
\* - Simplified logic of comparing Tendermint heights
\*
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS Integers, FiniteSets

\******************************************************************************
\* Type definitions
\******************************************************************************

\* @typeAlias: CHAIN_ID = Str;
\* @typeAlias: CLIENT_ID = Int;
\* @typeAlias: CONNECTION_ID = Int;
\* @typeAlias: HEIGHT = [ revision_number: Int, revision_height: Int ];
\* @typeAlias: CLIENT = [ heights: Set(HEIGHT) ];
\* @typeAlias: CLIENTS = CLIENT_ID -> CLIENT;
\*
\* @typeAlias: CONNECTION = [ state: Str, chainId: CHAIN_ID, clientId: CLIENT_ID,
\*   connectionId: CONNECTION_ID, counterpartyChainId: CHAIN_ID,
\*   counterpartyClientId: CLIENT_ID, counterpartyConnectionId: CONNECTION_ID ];
\* @typeAlias: CONNECTIONS = CONNECTION_ID -> CONNECTION;
\*
\* @typeAlias: ACTION = [ type: Str, chainId: CHAIN_ID, clientState: HEIGHT, consensusState: HEIGHT,
\*   clientId: CLIENT_ID, header: HEIGHT, previousConnectionId: Int, counterpartyChainId: CHAIN_ID,
\*   counterpartyClientId: CLIENT_ID, counterpartyConnectionId: Int];
\* @typeAlias: OUTCOME = Str;
\*
\* @typeAlias: CHAIN = [ height: HEIGHT, clients:  CLIENTS, clientIdCounter: Int,
\*   connections: CONNECTIONS, connectionIdCounter: Int, connectionProofs: Set(ACTION) ];
\* @typeAlias: CHAINS = CHAIN_ID -> CHAIN;
\* 
Typedefs == TRUE


\******************************************************************************
\* Constants (define the state space size) 
\* Variables (define the decompoistion of the state space into components)
\******************************************************************************

CONSTANTS
  \* @type: Set(CHAIN_ID); ids of existing chains
  ChainIds,
  \* @type: Int; max revision which chains can reach 
  MaxRevisionNumber,
  \* @type: Int; max height which chains can reach for any given revision
  MaxRevisionHeight,
  \* @type: Int; max number of client to be created per chain
  MaxClientsPerChain,
  \* @type: Int; max number of connections to be created per chain
  MaxConnectionsPerChain

\* @type: Set(CLIENT_ID); set of possible client identifiers
ClientIds == 0..(MaxClientsPerChain - 1)

\* @type: Set(CONNECTION_ID); set of possible connection identifiers
ConnectionIds == 0..(MaxConnectionsPerChain - 1)

\* @type: Set(HEIGHT); set of possible height tuples
Heights == [ revision_number: (1..MaxRevisionNumber), revision_height: (1..MaxRevisionHeight) ]

\* @type: HEIGHT;
ZeroHeight == [ revision_number |-> 0, revision_height |-> 0 ]

\* @type: HEIGHT;
MaxChainHeight == [ revision_number |-> MaxRevisionNumber, revision_height |-> MaxRevisionHeight ]

\* if a chain identifier is not set then it is "-1"
ChainIdNone == "-1"
\* if a client identifier is not set then it is -1
ClientIdNone == -1
\* if a connection identifier is not set then it is -1
ConnectionIdNone == -1


VARIABLES
  \* @type: CHAINS; mapping from chain id to its data
  chains,
  \* This joins together fields of all possible actions (will be replaced with disjoint unions in the future)
  \* @type: ACTION;
  action,
  \* @type: OUTCOME;
  actionOutcome


\******************************************************************************
\* Tendermint heights
\******************************************************************************
\* This is an implementation of the height comparison for Tendermint heights,
\* which include a revision (client version) and a block height.
\* The comparison is lexicographic for tuples (revision_number, revision_height)

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightLT(a, b) ==
    \/ a.revision_number < b.revision_number
    \/ (a.revision_number = b.revision_number /\ a.revision_height < b.revision_height)

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightLTE(a, b) == HeightLT(a, b) \/ a = b

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightGT(a, b)  == ~ HeightLTE(a, b)

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightGTE(a, b) == ~ HeightLT(a, b)

\* Checks if the block is higher but the revision is the same
\* @type: (HEIGHT, HEIGHT) => Bool;
HigherRevisionHeight(a, b) ==
    /\ a.revision_number = b.revision_number
    /\ a.revision_height > b.revision_height

\* Checks if the revision is higher
\* @type: (HEIGHT, HEIGHT) => Bool;
HigherRevisionNumber(a, b) ==
    /\ a.revision_number > b.revision_number

\* @type: (HEIGHT) => Bool;
IsMaxRevisionNumber(h) == h.revision_number = MaxRevisionNumber

\* @type: (HEIGHT) => Bool;
IsMaxRevisionHeight(h) == h.revision_height = MaxRevisionHeight

\* @type: (Set(HEIGHT)) => HEIGHT;
ChooseMaxHeight(S) == CHOOSE x \in S: \A y \in S: HeightLTE(y, x)


\***************************************************************
\* Protocol methods 
\***************************************************************

\* A success outcome, common for all protocol methods
Success == "Success"

\* Possible error outcomes
ErrorChainNotFound == "ErrorChainNotFound"
ErrorClientExists == "ErrorClientExists"
ErrorMaxClientsReached == "ErrorMaxClientsReached"
ErrorClientNotFound == "ErrorClientNotFound"
ErrorHeaderVerificationFailure == "ErrorHeaderVerificationFailure"


\* set of possible connection states
ConnectionStates == {
    "Uninitialized",
    "Init",
    "TryOpen",
    "Open"
}


\***************************************************************
\* ICS02/ICS07 (Client) protocol methods and their expected results
\***************************************************************

\* @type: (CHAIN_ID, HEIGHT) => OUTCOME;
CreateClientResult(chainId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN ErrorChainNotFound
  ELSE IF chains[chainId].clientIdCounter \in DOMAIN chains[chainId].clients
    THEN ErrorClientExists
  ELSE IF chains[chainId].clientIdCounter >= MaxClientsPerChain 
    THEN ErrorMaxClientsReached
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


\* @type: (CHAIN_ID, CLIENT_ID, HEIGHT) => OUTCOME;
UpdateClientResult(chainId, clientId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN ErrorChainNotFound
  ELSE IF clientId \notin DOMAIN chains[chainId].clients
    THEN ErrorClientNotFound
  ELSE IF ~HigherRevisionHeight(height, ChooseMaxHeight(chains[chainId].clients[clientId].heights))
    THEN ErrorHeaderVerificationFailure
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


\* @type: (CHAIN_ID, CLIENT_ID, HEIGHT) => OUTCOME;
UpgradeClientResult(chainId, clientId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN ErrorChainNotFound
  ELSE IF clientId \notin DOMAIN chains[chainId].clients
    THEN ErrorClientNotFound
  ELSE IF ~HigherRevisionHeight(height, ChooseMaxHeight(chains[chainId].clients[clientId].heights))
    THEN ErrorHeaderVerificationFailure
  ELSE Success

\* @type: (CHAIN_ID, CLIENT_ID, HEIGHT) => Bool;
UpgradeClient(chainId, clientId, height) ==
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
    /\ LET result == CreateClientResult(chainId, height) IN 
        actionOutcome' = result /\
        IF result = Success THEN
          CreateClient(chainId, height)
        ELSE
          UNCHANGED chains

UpdateClientAction ==
  \E chainId \in ChainIds:
  \E clientId \in ClientIds:
  \E height \in Heights:
    /\ action' = [ type |-> "UpdateClient", chainId |-> chainId, clientId |-> clientId, height |-> height ]
    /\ LET result == UpdateClientResult(chainId, clientId, height) IN 
        actionOutcome' = result /\
        IF result = Success THEN
          UpdateClient(chainId, clientId, height)
        ELSE
          UNCHANGED chains
CInit ==
  /\ ChainIds = {"chainA", "chainB"}
  /\ MaxRevisionNumber = 3
  /\ MaxRevisionHeight = 3
  /\ MaxClientsPerChain = 3
  /\ MaxConnectionsPerChain = 3

\* @type: () => CLIENT;
EmptyClient == [ heights |-> {} ]

\* @type: () => CONNECTION;
EmptyConnection == [ 
  state |-> "None", chainId |-> "None", clientId |-> 0, connectionId |-> 0,
  counterpartyChainId |-> "None", counterpartyClientId |-> 0, counterpartyConnectionId |-> 0 ]

\* @type: () => CHAIN;
EmptyChain == [
  height |-> ZeroHeight,
  clients |-> [ clientId \in {} |-> EmptyClient ],
  clientIdCounter |-> 0,
  connections |-> [ connectionId \in {} |-> EmptyConnection ],
  connectionIdCounter |-> 0,
  connectionProofs |-> {}
]

Init ==
  \* create a client and a connection with none values
  LET 
    \* @type: CLIENT;
    clientNone == [
      heights |-> {}
  ] IN
  LET 
      \* @type: CONNECTION;
      connectionNone == [
      state |-> "Uninitialized",
      chainId |-> ChainIdNone,
      clientId |-> ClientIdNone,
      connectionId |-> ConnectionIdNone,
      counterpartyChainId |-> ChainIdNone,
      counterpartyClientId |-> ClientIdNone,
      counterpartyConnectionId |-> ConnectionIdNone
  ] IN
  \* create an empty chain
  LET 
      \* @type: CHAIN;
      emptyChain == [
      height |-> [ revision_number |-> 1, revision_height |-> 1 ],
      clients |-> [clientId \in ClientIds |-> clientNone],
      clientIdCounter |-> 0,
      connections |-> [connectionId \in ConnectionIds |-> connectionNone],
      connectionIdCounter |-> 0,
      connectionProofs |-> {}
  ] IN
  /\ chains = [chainId \in ChainIds |-> emptyChain]
  /\ action = [type |-> "None"]
  /\ actionOutcome = "None"

Next ==
  \/ CreateClientAction
  \/ UpdateClientAction

TestMaxChainHeight == 
  \E c \in ChainIds:
    IsMaxRevisionHeight(chains[c].height)

InvTestMaxChainHeight == ~TestMaxChainHeight

===============================================================================
