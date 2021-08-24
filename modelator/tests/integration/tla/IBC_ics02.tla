------------------------------- MODULE IBC_ics02 ----------------------------------

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
  chains


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


\* @type: (CHAIN_ID, Int) => Str;
CreateClientErrors(chainId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN "Chain not found"
  ELSE IF chains[chainId].clientIdCounter \in DOMAIN chains[chainId].clients
    THEN "Client already exists"
  ELSE IF chains[chainId].clientIdCounter >= MaxClientsPerChain 
    THEN "Maximum number of clients reached"
  ELSE ""

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
UpdateClientErrors(chainId, clientId, height) ==
  IF chainId \notin DOMAIN chains 
    THEN "Chain not found"
  ELSE IF clientId \notin DOMAIN chains[chainId].clients
    THEN "Client not found"
  ELSE IF Max(chains[chainId].clients[clientId].heights) >= height
    THEN "Height too small"
  ELSE ""

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


CreateClientAction(chainId) ==
  \E height \in Heights:
    LET error == CreateClientErrors(chainId, height) IN 
    IF error = "" THEN
      CreateClient(chainId, height)
    ELSE
      UNCHANGED chains

UpdateClientAction(chainId) ==
  \E clientId \in ClientIds:
  \E height \in Heights:
    LET error == UpdateClientErrors(chainId, clientId, height) IN 
    IF error = "" THEN
      UpdateClient(chainId, clientId, height)
    ELSE
      UNCHANGED chains

CInit ==
  /\ ChainIds = {"chainA", "chainB"}
  /\ MaxChainHeight = 3
  /\ MaxClientsPerChain = 3

\* @type: () => CLIENT;
EmptyClient == [ heights |-> {} ]

\* @type: () => CHAIN;
EmptyChain == [
  height |-> 1,
  clients |-> [ clientId \in {} |-> EmptyClient ],
  clientIdCounter |-> 0
]

Init ==
  chains = [ chainId \in ChainIds |-> EmptyChain ]


Next == 
  \E chainId \in ChainIds:
    \/ CreateClientAction(chainId)
    \/ UpdateClientAction(chainId)

===============================================================================
