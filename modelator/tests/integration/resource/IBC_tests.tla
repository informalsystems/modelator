------------------------------- MODULE IBC_tests ----------------------------------
\* The IBC models, simplified from 
\* https://github.com/informalsystems/ibc-rs/tree/v0.8.0/modules/tests/support/model_based,
\* originally constructed by Vitor Enes, with additions by Jehan Tremback
\*
\* This file contains declarations of constants, state variables, and utility functions.
\* For protocol-specific methods see IBC_icsXX.tla files.
\* For execution environment (Init & Next), invariants, and tests see IBC_tests.tla.
\*
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS Integers, FiniteSets

VARIABLES
  \* @typeAlias: CHAIN_ID = Str;
  \* @typeAlias: CLIENT_ID = Int;
  \* @typeAlias: HEIGHT = [ revision_number: Int, revision_height: Int ];
  \* @typeAlias: CLIENT = [ heights: Set(HEIGHT) ];
  \* @typeAlias: CLIENTS = CLIENT_ID -> CLIENT;
  \* @typeAlias: CHAIN = [ height: HEIGHT, clients:  CLIENTS, clientIdCounter: Int ];
  \* @typeAlias: CHAINS = CHAIN_ID -> CHAIN;
  \* 
  \* @type: CHAINS; mapping from chain id to its data
  chains,
  \* This joins together fields of all possible actions (will be replaced with disjoint unions in the future)
  \* @type: [type: Str, chainId: CHAIN_ID, clientId: CLIENT_ID, height: Int];
  action,
  \* @type: Str;
  actionOutcome


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

\* @type: Set(HEIGHT); set of possible height tuples
Heights == [ revision_number: (1..MaxRevisionNumber), revision_height: (1..MaxRevisionHeight) ]

\* @type: HEIGHT;
MaxHeight == [ revision_number |-> MaxRevisionNumber, revision_height |-> MaxRevisionHeight ]

(******************************** Tendermint heights **********************************)
\* This is an implementation of the height comparison for Tendermint heights,
\* which include a revision (client version) and a block height.
\* The comparison is lexicographic for tuples (revision_number, revision_height)
\* @type: (HEIGHT, HEIGHT) => Bool
HeightLT(a, b) ==
    \/ a.revision_number < b.revision_number
    \/ (a.revision_number = b.revision_number /\ a.revision_height < b.revision_height)
\* @type: (HEIGHT, HEIGHT) => Bool
HeightLTE(a, b) == HeightLT(a, b) \/ a = b
\* @type: (HEIGHT, HEIGHT) => Bool
HeightGT(a, b)  == ~ HeightLTE(a, b)
\* @type: (HEIGHT, HEIGHT) => Bool
HeightGTE(a, b) == ~ HeightLT(a, b)

\* Checks if the block is higher but the revision is the same
\* @type: (HEIGHT, HEIGHT) => Bool
HigherRevisionHeight(a, b) ==
    /\ a.revision_number = b.revision_number
    /\ a.revision_height > b.revision_height

\* Checks if the revision is higher
\* @type: (HEIGHT, HEIGHT) => Bool
HigherRevisionNumber(a, b) ==
    /\ a.revision_number > b.revision_number

\* @type: (Set(HEIGHT)) => HEIGHT
MaxHeight(S) == CHOOSE x \in S: \A y \in S: HeightLTE(y, x)


\* A success outcome, common for all protocol methods
Success == "Success"


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
