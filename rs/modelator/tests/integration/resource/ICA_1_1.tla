------------------------------- MODULE ICA_1_1 ----------------------------------
\* Interchain Accounts (ICA) model, Variant 1
\* 2021 Andrey Kuprianov, Informal Systems
\* 
\* This is the extension of Variant 0, contained in ICA_0.tla
\* In this model we focus as follows:
\* - We abstract system interactions to the most coarse-grained actions
\*    - This is very useful to understand the system dynamics from bird's-eye view
\* - We model system data relashionships up to the degree necessary 
\*   to properly express the coarse-grained system actions
\*
\* Where to get the coarse-grained system actions from?
\* - One possibility is "Take the user-visible actions"
\* - Another is "Take a look at the specification structure";
\*   e.g. https://git.io/J1BRE gives us a hint by describing
\*   > Register & Controlling flows
\*   which also coincides with the user-visible actions:
\*   - CreateInterchainAccount: abstracts interactions between controller and host chains,
\*     representing only their combined preconditions & effects
\*     - In the real ICA, an interchain account is created by executing a sequence of steps:
\*       1. InitIterchainAccount (controller chain)
\*       2. OnChanOpenInit (controller chain)
\*       3. OnChanOpenTry (host chain)
\*       4. OnChanOpenAck (controller chain)
\*       5. OnChanOpenConfirm (host chain)
\*   - SendInterchainTransaction: an abstraction of sending a Cosmos transaction 
\*     from controller chain, and excuting it on the host chain
\*     - In the real ICA, this is done in a sequence of steps:
\*       1. TrySendTx / createOutgoingPacket (controller chain)
\*       2. OnRecvPacket / AuthenticateTx / ExecuteTx (host chain)
\*       

EXTENDS Integers, FiniteSets

\*[1] We extend the data relashionships to those neccessary for coarse-grained actions:
\*    - Multiple chains
\*    - IBC connections: https://github.com/cosmos/ibc/tree/master/spec/core/ics-003-connection-semantics
\*    - IBC ports and channels: https://github.com/cosmos/ibc/tree/master/spec/core/ics-004-channel-and-packet-semantics
\*    - active channels: a map from ICA ports to active channels used for those ports

\******************************************************************************
\* Type definitions
\******************************************************************************
\* @typeAlias: CHAIN_ID = Str;
\* @typeAlias: CONNECTION_ID = Int;
\* @typeAlias: CHANNEL_ID = Int;
\* @typeAlias: ADDRESS = Str;
\* @typeAlias: MODULE = Str;
\* A port is a record with 3 fields, as defined by ICA
\* @typeAlias: PORT = [ connId: CONNECTION_ID, cpConnId: CONNECTION_ID, owner: ADDRESS ];
\* @typeAlias: PORTS = PORT -> MODULE;
\* A connection contains the counterparty chain id and counterparty connection id
\* @typeAlias: CONNECTION = [ cpChainId: CHAIN_ID, cpConnId: CONNECTION_ID ];
\* @typeAlias: CONNECTIONS = CONNECTION_ID -> CONNECTION;
\* A channel is bound to a specific connection id, a port, and has counterparty channel id and port id
\* @typeAlias: CHANNEL = [ connId: CONNECTION_ID, port: PORT, cpChannelId: CHANNEL_ID, cpPort: PORT ];
\* @typeAlias: CHANNELS = CHANNEL_ID -> CHANNEL;
\* @typeAlias: ACTIVE_CHANNELS = PORT -> CHANNEL_ID;
\*
\* @typeAlias: CHAIN = [ ports: PORTS, connections: CONNECTIONS, channels: CHANNELS, 
\*                       nextConnectionId: Int, nextChannelId: Int, 
\*                       activeChannels: ACTIVE_CHANNELS, accounts: Set(PORT) ];
\* @typeAlias: CHAINS = CHAIN_ID -> CHAIN;
\*
\* @typeAlias: OUTCOME = Str;
Typedefs == TRUE

\******************************************************************************
\* Variables (define the decompoistion of the state space into components)
\******************************************************************************
VARIABLES
  \* @type: CHAINS; mapping from chain id to the chain data
  chains,
  \* @type: [ type: Str,  
  \*   port: PORT, module: MODULE,  
  \*   connId: CONNECTION_ID, cpConnId: CONNECTION_ID, owner: ADDRESS ];
  action,
  
  \* @type: OUTCOME;
  outcome


\******************************************************************************
\* Constants (define the state space size) 
\******************************************************************************
CONSTANTS
  \* @type: Set(CHAIN_ID); set of chain identifiers
  ChainIds,
  \* @type: Set(ADDRESS); set of account addresses
  Addresses,
  \* @type: Set(MODULE); ids of existing modules
  Modules,
  \* @type: CONNECTION_ID; maximum connection id
  MaxConnectionId,
  \* @type: CHANNEL_ID; maximum channel id
  MaxChannelId

\******************************************************************************
\* Sets and enumerations
\******************************************************************************

ICAModule == "interchain-accounts"
OtherModule == "other-module"

\* @type: () => Set(CONNECTION_ID);
ConnectionIds == 0 .. MaxConnectionId

\* @type: () => Set(CHANNEL_ID);
ChannelIds == 0 .. MaxChannelId

\* @type: () => Set(PORT);
Ports == [
  connId: ConnectionIds,
  cpConnId: ConnectionIds,
  owner: Addresses
]

\* @type: (CONNECTION_ID, CONNECTION_ID, ADDRESS) => PORT;
Port(connId, cpConnId, owner) == [ connId |-> connId, cpConnId |-> cpConnId, owner |-> owner]

\* @type: () => PORT; default port of ICA module
ICAPort == Port(0,0,"ICAModule")

\*[2] Our actions get more complex, in particular they may now fail because of multiple reasons
\*    - Having a precondition that returns a simple boolean value is no longer enough
\*      - Indeed, when testing a model execution against an implementation,
\*        you want to make sure that the implementation returns the expected error
\*    - Thus we switch from boolean action preconditions to expected action outcomes

\*[3] We use the actual implementation for creating the model.
\*    - While specifications are useful, we've seen much too often when specs and code diverge
\*    - The semantics of what happens in the code is most often precise,
\*      while specifications are in plain English, and thus in many cases do not posess strict semantics
\*    - The models constructed from the code are structured accordingly, 
\*      and thus can be later easily used to perform model-based testing of the implementation

\******************************************************************************
\* Actions
\******************************************************************************

\* Possible action outcomes
OK == "OK"
ErrPortBound == "Port already bound"
ErrActiveChannelExists == "Active channel already exists"
ErrConnectionExists == "Connection already exists"
ErrMalformedConnection == "Malformed connection"
ErrMaxChannelReached == "Can't create a new channel: maximum number of channels reached"

\* @type: (PORTS, PORT, MODULE) => PORTS;
AddPort(ports, port, module) == 
  [ p \in DOMAIN ports \union {port} |-> 
    IF p = port THEN module ELSE ports[p]
  ]


\* @type: (CONNECTIONS, CONNECTION_ID, CHAIN_ID, CONNECTION_ID) => CONNECTIONS;
AddConnection(connections, connId, cpChainId, cpConnId) == 
  [ c \in DOMAIN connections \union {connId} |-> 
    IF c = connId THEN [ cpChainId |-> cpChainId, cpConnId |-> cpConnId ]
    ELSE connections[c]
  ]

\* @type: (CHANNELS, CHANNEL_ID, PORT, CONNECTION_ID, CHANNEL_ID, PORT) => CHANNELS;
AddChannel(channels, channelId, port, connId, cpChannelId, cpPort) == 
  [ c \in DOMAIN channels \union {channelId} |-> 
    IF c = channelId THEN [ connId |-> connId, port |-> port, cpChannelId |-> cpChannelId, cpPort |-> cpPort ]
    ELSE channels[c]
  ]

\* @type: (ACTIVE_CHANNELS, PORT, CHANNEL_ID) => ACTIVE_CHANNELS;
AddActiveChannel(activeChannels, port, channelId) == 
  [ p \in DOMAIN activeChannels \union {port} |-> 
    IF p = port THEN channelId ELSE activeChannels[p]
  ]


\* @type: (CHAIN_ID, CONNECTION_ID, CONNECTION_ID, ADDRESS) => OUTCOME;
CreateInterchainAccountOutcome(chainId, connId, cpConnId, owner) ==
  LET port == Port(connId, cpConnId, owner) IN 
  LET chain == chains[chainId] IN
  LET cpChainId == chain.connections[connId].cpChainId IN
  LET cpChain == chains[cpChainId] IN
    IF connId \notin DOMAIN chain.connections 
       \/ cpConnId \notin DOMAIN cpChain.connections
       \/ chain.connections[connId].cpChainId /= cpChainId
       \/ chain.connections[connId].cpConnId /= cpConnId
       \/ cpChain.connections[cpConnId].cpChainId /= chainId
       \/ cpChain.connections[cpConnId].cpConnId /= connId
      THEN ErrMalformedConnection
    ELSE IF chain.nextChannelId > MaxChannelId \/ cpChain.nextChannelId > MaxChannelId
      THEN ErrMaxChannelReached
    \* Controller chain
    \* account.go::InitInterchainAccount(): https://git.io/J1Bnt
    \* - the most important check here is that the port is not yet bound
    ELSE IF port \in DOMAIN chain.ports
      THEN ErrPortBound
    \* handshake.go::OnChanOpenInit(): https://git.io/J1Bn2
    \* - Most checks are simple identifier match validation
    \* - The most interesting check from the logical perspective is this: 
    \*   > activeChannelID, found := k.GetActiveChannelID(ctx, portID)
    \*   > if found { ... "existing active channel" ... }
    \* - At this point we realize that we need to track active ICA channels in the chains variable
    ELSE IF port \in DOMAIN chain.activeChannels
      THEN ErrActiveChannelExists
    ELSE OK 


\* @type: (CHAIN_ID, CONNECTION_ID, CONNECTION_ID, ADDRESS) => Bool;
CreateInterchainAccount(chainId, connId, cpConnId, owner) ==
  LET port == Port(connId, cpConnId, owner) IN 
  LET chain == chains[chainId] IN
  LET channelId == chain.nextChannelId IN
  LET cpChainId == chain.connections[connId].cpChainId IN
  LET cpChain == chains[cpChainId] IN
  LET cpChannelId == cpChain.nextChannelId IN
  chains' = [chains EXCEPT 
    \* Controller chain
    ![chainId] = [ @ EXCEPT
      \* Create a channel in one step
      !.nextChannelId = @ + 1,
      !.channels = AddChannel(@, channelId, port, connId, cpChannelId, ICAPort),
      \* account.go::InitInterchainAccount(): https://git.io/J1Bnt
      !.ports  = AddPort(@, port, ICAModule)
      \* \* handshake.go::OnChanOpenAck(): https://git.io/J1gEV
      \* !.activeCannels = AddActiveChannel(@, port, channelId),
      \* !.accounts = @ \union {port}
    ],
    \* Host chain
    ![cpChainId] = [ @ EXCEPT
      \* Create a channel in one step
      !.nextChannelId = @ + 1,
      !.channels = AddChannel(@, cpChannelId, ICAPort, cpConnId, channelId, port),
      \* handshake.go::OnChanOpenTry(): https://git.io/J1glm
      \* Most of the code here is irrelevant for coarse-grained actions:
      \* - The channel negotiation logic is invisible from outside, and all checks are vacuosly true
      \* - The only interesting part is registration of a new ICA account and address:
      \*   - everything is deterministically derived from port id; from the logical perspective,
      \*     it amounts to whether the host chain has seen this port before or not.
      \*   - this is again the place where we realise that our chain data ins incomplete:
      \*     we extend it to holds registered ICA accounts (which are just ports)
      !.accounts = @ \union {port},
      \* handshake.go::OnChanOpenConfirm(): https://git.io/J1gyE
      !.activeCannels = AddActiveChannel(@, port, cpChannelId)
    ]  
  ]

CreateInterchainAccountAction ==
  \E chainId \in ChainIds:
  \E connId \in ConnectionIds:
  \E cpConnId \in ConnectionIds:
  \E owner \in Addresses:
  /\ action' = [type |-> "CreateInterchainAccount", chainId |-> chainId, connId |-> connId, cpConnId |-> cpConnId, owner |-> owner]
  /\ LET res == CreateInterchainAccountOutcome(chainId, connId, cpConnId, owner) IN 
     /\ outcome' = res
     /\ IF res = OK THEN CreateInterchainAccount(chainId, connId, cpConnId, owner)
        ELSE  UNCHANGED chains

\* @type: (CHAIN_ID, CHAIN_ID) => OUTCOME;
CreateConnectionOutcome(chainId, cpChainId) ==
  LET chain == chains[chainId] IN
  LET cpChain == chains[cpChainId] IN
    IF \E connId \in DOMAIN chain.connections: 
      chain.connections[connId].cpChainId = cpChainId
      THEN ErrConnectionExists
    ELSE IF chainId = cpChainId
      THEN "Same chain"
    ELSE OK

\* @type: (CHAIN_ID, CHAIN_ID) => Bool;
CreateConnection(chainId, cpChainId) ==
  LET chain == chains[chainId] IN
  LET cpChain == chains[cpChainId] IN
  LET connId == chain.nextConnectionId IN
  LET cpConnId == cpChain.nextConnectionId IN
    chains' = [chains EXCEPT 
      ![chainId] = [ @ EXCEPT
        !.nextConnectionId = @ + 1,
        !.connections = AddConnection(@, connId, cpChainId, cpConnId)
      ],
      ![cpChainId] = [ @ EXCEPT
        !.nextConnectionId = @ + 1,
        !.connections = AddConnection(@, cpConnId, chainId, connId)
      ]
    ]

CreateConnectionAction ==
  \E chainId \in ChainIds:
  \E cpChainId \in ChainIds:
  /\ action' = [type |-> "CreateConnection", chainId |-> chainId, cpChainId |-> cpChainId]
  /\ LET res == CreateConnectionOutcome(chainId, cpChainId) IN 
     /\ outcome' = res
     /\ IF res = OK THEN CreateConnection(chainId, cpChainId)
        ELSE  UNCHANGED chains


\******************************************************************************
\* Init & Next
\******************************************************************************

ZeroPort == Port(0, 0, "")
ZeroConnection == [ cpChainId |-> "", cpConnId |-> 0 ]
ZeroChannel == [ connId |-> 0, port |-> ZeroPort, cpChannelId |-> 0, cpPort |-> ZeroPort ]

\* @type: () => CHAIN;
EmptyChain == 
  [ ports |-> [ p \in {ICAPort} |-> ICAModule ], 
    connections |-> [ c \in {} |-> ZeroConnection],
    channels |-> [ c \in {} |-> ZeroChannel],
    nextConnectionId |-> 1,
    nextChannelId |-> 1,
    activeChannels |-> [ p \in {} |-> 0 ],
    accounts |-> {}
  ]

Init == 
  /\ chains = [ chainId \in ChainIds |-> EmptyChain ]
  /\ action = [type |-> ""]
  /\ outcome = OK

Next == 
  \/ CreateInterchainAccountAction
  \/ CreateConnectionAction


\******************************************************************************
\* Test assertions & invariants
\******************************************************************************

TestCreateInterchainAccountSuccess == 
  /\ action.type = "CreateInterchainAccount"
  /\ outcome = OK

InvTestCreateInterchainAccountSuccess == ~TestCreateInterchainAccountSuccess

===============================================================================
