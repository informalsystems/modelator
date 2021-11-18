------------------------------- MODULE ICA_0 ----------------------------------
\* Interchain Accounts (ICA) model, Variant 0
\* 2021 Andrey Kuprianov, Informal Systems
\* 
\* This is the most basic variant, to get things started and to explain the general approach.
\* 
\* WHAT TO MODEL:
\*  - Often the amount of information in the system is overwhelming
\*  - For the model to be useful it is important to choose the right level of abstraction
\*  - We don't claim this is the only approach, but propose a certain way to focus your attention:
\*    - Choose the simplest executable action from your system
\*    - Describe in the model only what's necessary to reproduce it abstractly; omit everything else
\*    - This might be already enough to help you understand the system better, or even uncover some bugs
\*    - Gradually extend the model, by adding more actions & data relationships,
\*      but keep the more abstract variants around
\* 
\* Let's now apply this to Interchain Accounts.
\* We take the first executable action from the spec https://git.io/J1Yrm
\*   > Register Account Flow:
\*   >   The controller chain binds a new IBC port with an id composed of the 
\*   >   source/counterparty connection-ids & the interchain account owner address
\* 
\* We model only the necessary data relashionships for the above action (RegisterInterchainAccount)
\*   - A single controller chain (so no chains are modeled explicitely)
\*   - Addresses are unique identifiers for on-chain accounts
\*   - Connections are present, but do not connect anything
\*   - Port identifiers, for ICA  purposes, contain two connection ids, plus the owner address
\*   
\* VERY IMPORTANT: UNDERSTAND YOUR ENVIRONMENT
\*  - ICA module doesn't operate in a vacuum; e.g. the above action mentions binding IBC ports
\*  - Let's see what ICS05 (port allocation) says: https://git.io/J1Z4H
\*    - Ports are allocated first-come first-serve
\*    - Once a module has bound to a port, no other modules can use that port until the module releases it
\*  
\* The above entails, that to properly model interaction of ICA module with its environment,
\* we need to include in the model:
\*   - Other modules (one module different from ICA suffices)
\*   - BindPort action, that can be executed by any module (not only ICA)

\* We will guide you through certain steps in constructing your TLA+ model
\* suitable for model-based testing purposes
\* We are not saying this is the only possible way; simply the way we find convenient

\*[1] Download and install Apalache model checker: https://apalache.informal.systems
\*    Let's use a particular version: https://github.com/informalsystems/apalache/releases/tag/v0.17.4
\*[2] We will work with Apalache from the commnad line;
\*    it is convenient to set up an alias: `alias apalache=<APALACHE-PATH>/bin/apalache-mc`

\*[3] Usually any model needs to handle initegers and finite sets, so we "include" those
EXTENDS Integers, FiniteSets

\*[4] We start by describing our data types and their relashionhips
\*    using Apalache type annotations: https://apalache.informal.systems/docs/tutorials/snowcat-tutorial.html
\*    This feature is unique to Apalache, and we highly recommend to use it when writing your specs
\*    Try it: `apalache typecheck ICA_0.tla`

\******************************************************************************
\* Type definitions
\******************************************************************************
\* @typeAlias: ADDRESS = Str;
\* @typeAlias: MODULE = Str;
\* @typeAlias: CONNECTION_ID = Int;
\* A port is a record with 3 fields, as defined by ICA
\* @typeAlias: PORT = [ connId: CONNECTION_ID, otherConnId: CONNECTION_ID, owner: ADDRESS];
\* PORTS is a type that represents a mapping from a port to the owning module
\* @typeAlias: PORTS = PORT -> MODULE;
\* 
Typedefs == TRUE

\*[5] Describe the variables that the model has; each variable has a specific type
\*    - For this model variant, we track only which ports are assigned to which modules
\*      'action' and 'outcome' variables are special, and are needed to understand
\*      the executions produced from the model, and for model-based tests later.
\*    - Please ignore 'action' and 'outcome' variables for the time being

\******************************************************************************
\* Variables (define the decompoistion of the state space into components)
\******************************************************************************
VARIABLES
  \* @type: PORTS; mapping from port id to the owning module
  ports,
  \* @type: [ type: Str,  
  \*   port: PORT, module: MODULE,  
  \*   connId: CONNECTION_ID, otherConnId: CONNECTION_ID, owner: ADDRESS ];
  action,
  \* @type: Bool;
  outcome


\*[6] Define the search space for the model
\*    - In a nutshell, a model checker (e.g. Apalache) does nothing more than searching 
\*      over a large space of possible combinations of variable assignments
\*    - To describe this search space we define what's called constants
\*    - A model can be instantiated with different combination of constants;
\*      a particular set we use can be found in the file ICA_0.cfg

\******************************************************************************
\* Constants (define the search space size) 
\******************************************************************************
CONSTANTS
  \* @type: Set(ADDRESS); set of account addresses
  Addresses,
  \* @type: Set(MODULE); ids of existing modules
  Modules,
  \* @type: CONNECTION_ID; maximum connection id
  MaxConnectionId

\*[7] We introduce some useful shorhands:
\*    - identifiers instead of literal strings
\*    - declarations for frequently used sets
\*    - record constructors

\******************************************************************************
\* Sets and enumerations
\******************************************************************************

ICAModule == "interchain-accounts"
OtherModule == "other-module"

\* @type: () => Set(CONNECTION_ID);
ConnectionIds == 0 .. MaxConnectionId

\* @type: () => Set(PORT);
Ports == [
  connId: ConnectionIds,
  otherConnId: ConnectionIds,
  owner: Addresses
]

\* @type: (CONNECTION_ID, CONNECTION_ID, ADDRESS) => PORT;
Port(connId, otherConnId, owner) == [ connId |-> connId, otherConnId |-> otherConnId, owner |-> owner]


\*[8] We describe model actions
\*    Each action is represented by 3 components:
\*    - Precondition: is it legal to take an action in the current state? 
\*      (e.g. we can bind a port only if it's not bound already)
\*    - Update: _assuming_ the precondition holds, change the state
\*      (e.g. BindPort maps another port to the owning module)
\*    - Universal action: an action that can be taken with any inputs
\*      - action updates usually contain certain parameters
\*      - we _existentially quantlfy_ over those parameters, 
\*        i.e. allow to select any combination of values for them,
\*        like they come over a wire, and we don't know who and why sends them
\*      - we save selected parameters in the variable `action`, for later inspection
\*      - we check whether the precondition holds, and save it in the `outcome`
\*      - if the precondition holds, we execute the update, otherwise do nothing


\******************************************************************************
\* Actions
\******************************************************************************

\* @type: (PORT, MODULE) => Bool;
BindPortPre(port, module) ==
  port \notin DOMAIN ports

\* @type: (PORT, MODULE) => Bool;
BindPort(port, module) == 
  ports' = [ 
  p \in DOMAIN ports \union {port} |-> 
    IF p = port THEN module ELSE ports[p]
]

\* @type: () => Bool;
BindPortAction ==
  \E port \in Ports:
  \E module \in Modules:
  /\ action' = [type |-> "BindPort", port |-> port, module |-> module]
  /\ LET ok == BindPortPre(port, module) IN 
     /\ outcome' = ok
     /\ IF ok THEN BindPort(port, module)
        ELSE  UNCHANGED ports


\* @type: (CONNECTION_ID, CONNECTION_ID, ADDRESS) => Bool;
RegisterInterchainAccountPre(connId, otherConnId, owner) ==
  LET port == Port(connId, otherConnId, owner) IN 
  /\ BindPortPre(port, ICAModule)
  

\* @type: (CONNECTION_ID, CONNECTION_ID, ADDRESS) => Bool;
RegisterInterchainAccount(connId, otherConnId, owner) ==
  LET port == Port(connId, otherConnId, owner) IN 
  /\ BindPort(port, ICAModule)

RegisterInterchainAccountAction ==
  \E connId \in ConnectionIds:
  \E otherConnId \in ConnectionIds:
  \E owner \in Addresses:
  /\ action' = [type |-> "RegisterInterchainAccount", connId |-> connId, otherConnId |-> otherConnId, owner |-> owner]
  /\ LET ok == RegisterInterchainAccountPre(connId, otherConnId, owner) IN 
     /\ outcome' = ok
     /\ IF ok THEN RegisterInterchainAccount(connId, otherConnId, owner)
        ELSE  UNCHANGED ports

\*[9] We describe Init and Next predicates:
\*    - Init desrives initial state of our system 
\*      (e.g. no ports are bound)
\*    - Next describes what actions a model can execute at every step
\*      (in our case, any module can bind a port, or an ICA account can be registered)

\******************************************************************************
\* Init & Next
\******************************************************************************

\* @type: () => Bool;
Init == 
  /\ ports = [ p \in {} |-> ""]
  /\ action = [type |-> ""]
  /\ outcome = FALSE

Next == 
  \/ BindPortAction
  \/ RegisterInterchainAccountAction



\*[10] We describe test assertions: which executions we want to be generated from the model
\*     - In our case we describe two simple assertions, where each says that 
\*       "RegisterInterchainAccount" action should be taken,
\*       but one time with success, and another time with failure.
\*     - A technicality: model checkers talk about invariants,
\*       i.e. the assertions that should always hold.
\*     - We, on the contrary, describe executions that we want to see.
\*     - To get an invariant from a test assertion, we simply negate it.
\*     - A model checker tries to find an execution that violates that artificial invariant,
\*       and thus finds the execution that satisfies the original test assertion.

\******************************************************************************
\* Test assertions & invariants
\******************************************************************************

TestRegisterInterchainAccountSuccess == 
  /\ action.type = "RegisterInterchainAccount"
  /\ outcome = TRUE

InvTestRegisterInterchainAccountSuccess == ~TestRegisterInterchainAccountSuccess

TestRegisterInterchainAccountFailure == 
  /\ action.type = "RegisterInterchainAccount"
  /\ outcome = FALSE

InvTestRegisterInterchainAccountFailure == ~TestRegisterInterchainAccountFailure

\*[11] Run Apalache to generate the execution TestRegisterInterchainAccountSuccess:
\*     `apalache check --inv=InvTestRegisterInterchainAccountSuccess ICA_0.tla`
\* It will produce the following:

\* (* Initial state *)
\* State0 ==
\*   action = [type |-> ""] /\ outcome = FALSE /\ ports = [ x \in {} |-> x ]

\* (* Transition 2 to State1 *)
\* State1 ==
\*   action
\*       = [connId |-> 0,
\*         otherConnId |-> 0,
\*         owner |-> "a",
\*         type |-> "RegisterInterchainAccount"]
\*     /\ outcome = TRUE
\*     /\ ports
\*       = [connId |-> 0, otherConnId |-> 0, owner |-> "a"]
\*         :> "interchain-accounts"

\* (* The following formula holds true in the last state and violates the invariant *)
\* InvariantViolation ==
\*   action["type"] = "RegisterInterchainAccount" /\ outcome = TRUE

\*[12] Run Apalache to generate the execution TestRegisterInterchainAccountFailure:
\*     `apalache check --inv=InvTestRegisterInterchainAccountSuccess ICA_0.tla`
\* It will produce the following:

\* (* Initial state *)
\* State0 ==
\*   action = [type |-> ""] /\ outcome = FALSE /\ ports = [ x \in {} |-> x ]

\* (* Transition 0 to State1 *)
\* State1 ==
\*   action
\*       = [module |-> "other-accounts",
\*         port |-> [connId |-> 0, otherConnId |-> 1, owner |-> "a"],
\*         type |-> "BindPort"]
\*     /\ outcome = TRUE
\*     /\ ports
\*       = [connId |-> 0, otherConnId |-> 1, owner |-> "a"] :> "other-accounts"

\* (* Transition 3 to State2 *)
\* State2 ==
\*   action
\*       = [connId |-> 0,
\*         otherConnId |-> 1,
\*         owner |-> "a",
\*         type |-> "RegisterInterchainAccount"]
\*     /\ outcome = FALSE
\*     /\ ports
\*       = [connId |-> 0, otherConnId |-> 1, owner |-> "a"] :> "other-accounts"

\* (* The following formula holds true in the last state and violates the invariant *)
\* InvariantViolation ==
\*   action["type"] = "RegisterInterchainAccount" /\ outcome = FALSE

\*[13] What does the above execution tells you?
\*     - Even at this very abstract level, "RegisterInterchainAccount" may fail
\*     - Why? because some other module may bind a port for a particular owner address
\*     - Congratulations! You've found a DOS attack by modeling in TLA+!
\*     - The DOS attack is possible because the port format is too deterministic and predictable

\*[14] Stay tuned! We'll continue with the next variant, ICA_1.tla.

===============================================================================
