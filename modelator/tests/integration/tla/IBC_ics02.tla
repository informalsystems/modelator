------------------------------- MODULE IBC_ics02 ----------------------------------
\* This is a simplified model of IBC ICS02 from 
\* https://github.com/informalsystems/ibc-rs/tree/v0.7.0/modules/tests/support/model_based
\*
\* For each protocol Method there is:
\*  - Method operator, that "implements" the method state updates, 
\*    assuming the preconditions for it hold;
\*  - MethodOutcome operator checks for the method preconditions, and returns 
\*    "OK" if all preconditions are met, or the error description if not;
\*  - MethodAction operator that surrounds method's state updates with the logic
\*    that checks preconditions, and stores method arguments and outcome
\*    in the "action" and "actionOutcome" variables.
\* 2021 Andrey Kuprianov, Informal Systems


EXTENDS Integers, FiniteSets

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

\* mapping from chain id to its data
VARIABLE 
  \* @typeAlias: CHAIN_ID = Str;
  \* @typeAlias: CLIENT_ID = Int;
  \* @typeAlias: CLIENT = [ heights: Set(Int) ];
  \* @typeAlias: CLIENTS = CLIENT_ID -> CLIENT;
  \* @typeAlias: CHAIN = [ height: Int, clients:  CLIENTS, clientIdCounter: Int ];
  \* @typeAlias: CHAINS = CHAIN_ID -> CHAIN;
  \* @type: CHAINS;
  chains,
  \* @type: [type: Str, chainId: CHAIN_ID, clientId: CLIENT_ID, height: Int];
  action,
  \* @type: Str;
  actionOutcome


CONSTANTS
  \* @type: Int;
  MaxChainHeight,
  \* @type: Int;
  MaxClientsPerChain,
  \* @type: Set(CHAIN_ID);
  ChainIds

\* set of possible chain heights
Heights == 1..MaxChainHeight
\* set of possible client identifiers
ClientIds == 0..(MaxClientsPerChain - 1)


\* Protocol methods and their preconditions

\* @type: (CHAIN_ID, Int) => Str;
CreateClientOutcome(chainId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN "Chain not found"
  ELSE IF chains[chainId].clientIdCounter \in DOMAIN chains[chainId].clients
    THEN "Client already exists"
  ELSE IF chains[chainId].clientIdCounter >= MaxClientsPerChain 
    THEN "Maximum number of clients reached"
  ELSE "OK"

\* @type: (CHAIN_ID, Int) => Bool;
CreateClient(chainId, height) ==
  LET clientId == chains[chainId].clientIdCounter IN
  chains' = [chains EXCEPT 
    ![chainId] = [@ EXCEPT 
      !.height = @+1, 
      !.clientIdCounter = @+1,
      !.clients = [ c \in DOMAIN @ \union {clientId} |-> 
        IF c = clientId THEN [heights |-> {height}] ELSE @[c]]
    ]
  ]


\* @type: (CHAIN_ID, CLIENT_ID, Int) => Str;
UpdateClientOutcome(chainId, clientId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN "Chain not found"
  ELSE IF clientId \notin DOMAIN chains[chainId].clients
    THEN "Client not found"
  ELSE IF Max(chains[chainId].clients[clientId].heights) >= height
    THEN "Height too small"
  ELSE "OK"

\* @type: (CHAIN_ID, CLIENT_ID, Int) => Bool;
UpdateClient(chainId, clientId, height) ==
  chains' = [chains EXCEPT 
    ![chainId] = [@ EXCEPT 
      !.height = @+1, 
      !.clients = [@ EXCEPT 
        ![clientId] = [heights |-> @.heights \union {height}]
      ]
    ]
  ]

\* Protocol actions: boilerplate code that checks preconditions, executes updates,
\* and stores action and actionOutcome.

CreateClientAction(chainId) ==
  \E height \in Heights:
    /\ action' = [ type |-> "CreateClient", chainId |-> chainId, height |-> height ]
    /\ LET outcome == CreateClientOutcome(chainId, height) IN 
        actionOutcome' = outcome /\
        IF outcome = "OK" THEN
          CreateClient(chainId, height)
        ELSE
          UNCHANGED chains

UpdateClientAction(chainId) ==
  \E clientId \in ClientIds:
  \E height \in Heights:
    /\ action' = [ type |-> "UpdateClient", chainId |-> chainId, clientId |-> clientId, height |-> height ]
    /\ LET outcome == UpdateClientOutcome(chainId, clientId, height) IN 
        actionOutcome' = outcome /\
        IF outcome = "OK" THEN
          UpdateClient(chainId, clientId, height)
        ELSE
          UNCHANGED chains

CInit ==
  /\ ChainIds = {"chainA", "chainB"}
  /\ MaxChainHeight = 10
  /\ MaxClientsPerChain = 5

\* @type: () => CLIENT;
EmptyClient == [ heights |-> {} ]

\* @type: () => CHAIN;
EmptyChain == [
  height |-> 1,
  clients |-> [ clientId \in {} |-> EmptyClient ],
  clientIdCounter |-> 0
]

Init ==
  /\ chains = [ chainId \in ChainIds |-> EmptyChain ]
  /\ action = [ type |-> "None" ]
  /\ actionOutcome = "None"


Next == 
  \E chainId \in ChainIds:
    \/ CreateClientAction(chainId)
    \/ UpdateClientAction(chainId)


TestMaxChainHeight == 
  \E c \in ChainIds:
    chains[c].height = MaxChainHeight

InvTestMaxChainHeight == ~TestMaxChainHeight

TestClientWith3Heights ==
  \E c \in ChainIds:
    \E cl \in DOMAIN chains[c].clients:
      Cardinality(chains[c].clients[cl].heights) >= 3

InvTestClientWith3Heights == ~TestClientWith3Heights

TestChainWith2ClientsWith2Heights ==
  \E c \in ChainIds:
    \E cl1, cl2 \in DOMAIN chains[c].clients:
      /\ cl1 /= cl2
      /\ \A cl \in {cl1, cl2}:
          Cardinality(chains[c].clients[cl].heights) >= 2

InvTestChainWith2ClientsWith2Heights == ~TestChainWith2ClientsWith2Heights

===============================================================================
