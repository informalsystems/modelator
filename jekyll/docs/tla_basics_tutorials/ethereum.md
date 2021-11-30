---
title: Ethereum Exploit
description: Finding an exploit using Apalache
layout: default
parent: TLA+ Basics Tutorials
nav_order: 6
---

# Finding an Ethereum exploit using Apalache

**The .tla and other referenced files are included [here](https://github.com/informalsystems/modelator/tree/main/jekyll/docs/tla_basics_tutorials/models).**

In 'Hello World' we used TLC to check a simple model. Now we will walk through a real model. The model models part of the ERC20 Ethereum blockchain technical standard; in particular the model can be used to generate a trace which exploits the API to transfer funds to an attackers address. The model was written by Igor Konnov.

## Intro

This model builds on the skills gained in ['Hello World'](./hell_world) and ['Typechecking'](./typechecking).

The model variables use a richer set of data structures including integers, tuples, and key value maps (called functions in TLA+). The operator definitions are also more complicated, making more use of the LET statement to define helper operators inline. 

Finally, we will search for a more interesting behavior pattern than we did in 'Hello World': an execution that withdraws funds from a target wallet into an attackers wallet. We will see how TLA+ can be used to find vulnerabilities in a real system.

You will probably find the [cheatsheet](./tla+cheatsheet) useful while reading.

## The system we model

The system being modeled maintains addresses for blockchain wallets. It's possible to transfer funds between addresses by executing transactions on the blockchain. There is a pool which holds transactions that have been submitted for execution, but have not yet been executed; these are pending transactions. Additionally, it is possible for wallet owners to delegate the ability to transfer their funds to a third party. This functionality is used in [smart contracts](https://en.wikipedia.org/wiki/Smart_contract).

The Ethereum ERC20 standard defines an [API](https://eips.ethereum.org/EIPS/eip-20) for the system. The API has three calls

- `SubmitTransfer(sender, toAddr, value)`\
Submit a transfer order, sending `value` from the address of `sender` to `toAddr`. The order will only be processed if the balance of the `sender` address is at least `value`.
- `SubmitTransferFrom(sender, fromAddr, toAddr, value)`\
Submit a transfer order, sending `value` from `fromAddr` to `toAddr`. The order will only be processed if the balance of the `fromAddr` is at least `value` _and_ the owner of `fromAddr` has previously given permission for `sender` to send transactions on their behalf, via the _SubmitApprove(...)_ call.
- `SubmitApprove(sender, spender, value)`\
Submit an order allowing `spender` to transfer funds from `sender`'s address on their behalf, up to a total sum of `value`.

The orders are submitted to the pendingTransactions pool. While the pool is not empty the blockchain will select and execute orders from the pool in a non-deterministic order.

You may notice that the descriptions of the _Submit*_ API calls not totally clear with respect to ordering and timing. We will see that this is exactly the problem with the API.

## Defining State

We isolate parts of the blockchain system relevant to the behavior we are trying to understand. For the purpose of verifying the API we should track 

- A set of blockchain addresses
- The balance of each address
- For each pair of addresses (A, B), the value address A has allowed address B to transfer to third parties on their behalf
- The pool of pending transactions

### Data Declarations

Apalache lets you define type aliases in a typedefs.tla file. You import them all at once using the EXTEND keyword in other .tla files. We define aliases for an ADDR (address) and TX (transaction) type.

```tla
\* (In typedefs.tla)

(*

An account address, in our case, simply an uninterpreted string:
@typeAlias: ADDR = Str;

A transaction (a la discriminated union but all fields are packed together):
@typeAlias: TX = [
    tag: Str,
    id: Int,
    fail: Bool,
    sender: ADDR,
    spender: ADDR,
    fromAddr: ADDR,
    toAddr: ADDR,
    value: Int
];

*)
```

We define ADDR as an alias for the builtin Str string type. We define TX as a composition of built in types and other aliases. In this case TX is a _record_ (struct) with types associated to keys.

For the state we define variables

```tla
VARIABLES
    \*
    \* Token balance for every account. This is exactly as `balanceOf` in ERC20.
    \* @type: ADDR -> Int;
    balanceOf,
    \*
    \* Allowance to transfer tokens
    \* from owner (1st element) by spender (2nd element).
    \* This is exactly as `allowance` of ERC20.
    \* @type: <<ADDR, ADDR>> -> Int;
    allowance,
    \*
    \* Pending transactions to be executed against the contract.
    \* Note that we have a set of transactions instead of a sequence,
    \* as the order of transactions on Ethereum is not predefined.
    \* To make it possible to submit two 'equal' transactions,
    \* we introduce a unique transaction id.
    \* @type: Set(TX);
    pendingTransactions,
    \*
    \* The last executed transaction.
    \* @type: TX;
    lastTx,
    \*
    \* A serial number to assign unique ids to transactions
    \* @type: Int;
    nextTxId
```

Breaking them down we have

- balanceOf with type `ADDR -> Int`\
This is Apalache's notation for specifying function (key value map) types. balanceOf is a function mapping addresses (ADDR) to integers (Int).
- allowance with type `<<ADDR, ADDR>> -> Int`\
Each allowance is an association between an allowing address, the allowed address, and the value that the allowing address allows the allowed address to transfer. We can store this as a function mapping pairs (<<T,T>>) to integers.
- pendingTransactions with type `Set(TX)`\
The pendingTransactions pool is a set, as it has no concept of order. In this case it is a set of the TX type that we defined an alias for earlier. 
- lastTx with type `TX`\
The model checker will always give you traces as a sequence of states. It can be useful to have additional information to understand why one state follows another in the sequence. Storing additional state variables can be useful if they record the _reason_ that the state changed the way it did. Saving the last processed transaction in the lastTx variable will make it easier for us to infer the flow of transactions in a trace.
- nextTxId with type `Int`\
We would like to have multiple identical transactions in the pendingTransactions pool. We modeled the pool as a set, which can only store one of a given value. Adding a unique id to transactions lets us store multiple logically identical transactions in the pool.

The absolute values of the addresses in the system are unimportant and we can model a fixed number of addresses without it affecting API interactions. This means we can define an immutable set of ADDR types: an operator taking no input and giving us a fixed set of addresses.

```tla
\* @type: () => Set(ADDR);
ADDRESSES == { "addr1", "addr2", "addr3" }
```

### Data Definitions

We have declared the data in the system but not defined concrete values. In particular we should define initial values for the variables.

```tla
Init ==
    \* every address has a non-negative number of tokens
    /\ balanceOf \in [ADDRESSES -> Nat]
    \* no account is allowed to withdraw from another account
    /\ allowance = [ pair \in ADDRESSES \X ADDRESSES |-> 0 ]
    \* no pending transactions
    /\ pendingTransactions = {}
    /\ nextTxId = 0
    /\ lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
```

TLA+ syntax can be opaque. Step by step

- `balanceOf \in [ADDRESSES -> Nat]`\
balanceOf is _in_ the set of _all_ functions mapping addresses to natural numbers
- `allowance = [ pair \in ADDRESSES \X ADDRESSES |-> 0 ]`\
allowance is _the_ function whose keys are all the possible pairs of addresses, and whose values are all 0.
- `pendingTransactions = {}`\
pendingTransactions is the empty set
- `nextTxId = 0`\
nextTxId is 0
- `lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]`\
lastTx is the record mapping id to 0, tag to "None" and fail to FALSE

Remember: Init is a boolean function that will evaluate true for a subset of _all_ possible states. In this case Init will match (hold true for) states where

1. balanceOf is _a_ function mapping addresses to natural numbers
2. AND allowance is _the_ function mapping all pairs of addresses to 0
3. AND pendingTransactions is _the_ empty set
4. AND nextTxId is 0
5. AND lastTx is _exactly_ the record [ id |-> 0, tag |-> "None", fail |-> FALSE ]

The model checker will check _all_ systems whose initial state matches the above criteria!

## Defining Transitions

We have defined the variables in the system, now we must define transitions. The Next operator defines which transitions are allowed in the system.

```tla
Next ==
    \/ \E sender, toAddr \in ADDRESSES, value \in Int:
        SubmitTransfer(sender, toAddr, value)
    \/ \E sender, fromAddr, toAddr \in ADDRESSES, value \in Int:
        SubmitTransferFrom(sender, fromAddr, toAddr, value)
    \/ \E sender, spender \in ADDRESSES, value \in Int:
        SubmitApprove(sender, spender, value)
    \/ \E tx \in pendingTransactions:
        \/ /\ tx.tag = "transfer"
           /\ ProcessTransfer(tx)
        \/ /\ tx.tag = "transferFrom"
           /\ ProcessTransferFrom(tx)
        \/ /\ tx.tag = "approve"
           /\ ProcessApprove(tx)
```

There are 6 actions, or types of transition in the system. They are 

- SubmitTransfer(sender, toAddr, value)
- SubmitTransferFrom(sender, fromAddr, toAddr, value)
- SubmitApprove(sender, spender, value)
- ProcessTransfer(tx)
- ProcessTransferFrom(tx)
- ProcessApprove(tx)

The three _Submit*_ actions match the API calls and the _Process*_ actions define the processing of a pending transaction from the pendingTransactions pool.

The actions are written using parameterized operators, this makes the code more readable.

```tla
SubmitTx(tx) == 
    /\ pendingTransactions' = pendingTransactions \union { tx }
    /\ lastTx' = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
    /\ nextTxId' = nextTxId + 1
    /\ UNCHANGED <<balanceOf, allowance>>

SubmitTransfer(_sender, _toAddr, _value) == 
    SubmitTx([  
                id |-> nextTxId,
                tag |-> "transfer",
                fail |-> FALSE,
                sender |-> _sender,
                toAddr |-> _toAddr,
                value |-> _value
            ])

SubmitTransferFrom(_sender, _fromAddr, _toAddr, _value) == 
    SubmitTx([
                id |-> nextTxId,
                tag |-> "transferFrom",
                fail |-> FALSE,
                sender |-> _sender,
                fromAddr |-> _fromAddr,
                toAddr |-> _toAddr,
                value |-> _value
            ])

SubmitApprove(_sender, _spender, _value) == 
    SubmitTx([
                id |-> nextTxId,
                tag |-> "approve",
                fail |-> FALSE,
                sender |-> _sender,
                spender |-> _spender,
                value |-> _value
            ])
```

We see that each of the _Submit*_ operators delegates to the _SubmitTx(tx)_ operator. Each operator adds a new transaction of TX type to the pendingTransactions set (and increments the unique nextTxId). Each transaction is tagged with a string "transfer", "transferFrom" or "approve". This allows us to disambiguate transactions in the _Process*_ actions.

### ProcessTransfer

The _Process*_ actions make use of the LET keyword to define inline operators. Inline operators are analogous to local variables or lambda functions in typical programming languages.

```tla
ProcessTransfer(tx) == 
    /\ pendingTransactions' = pendingTransactions \ { tx }
    /\ UNCHANGED <<allowance, nextTxId>>
    /\  LET fail ==
          \/ tx.value < 0
          \/ tx.value > balanceOf[tx.sender]
          \/ tx.sender = tx.toAddr
        IN
        /\ lastTx' = [ tx EXCEPT !.fail = fail ]
        /\ IF fail
           THEN UNCHANGED balanceOf
           ELSE 
           \* transaction succeeds
           \* update the balances of the 'sender' and 'toAddr' addresses
           balanceOf' = [ 
               balanceOf EXCEPT
               ![tx.sender] = @ - tx.value,
               ![tx.toAddr] = @ + tx.value
           ]
```

ProcessTransfer takes a TX type tx, tagged with "transfer", as input. For a pair of states (CurrentState, NextState). In all cases where the ProcessTransfer action is taken, the tx is removed from pendingTransactions, and allowance and nextTxId do not change. Additionally, there _may_ be a change to the balanceOf variable.

_fail_ is defined as a boolean: the transaction will fail if the value field is negative, or if the value is greater than the senders balance, or if the sender tries to send funds to themself (tx.sender = tx.toAddr).

_fail_ is used: the lastTx variable in NextState (lastTx') must be equal to tx, except for in the .fail key - where it should match the value of the inline operator _fail_. The syntax [ f EXCEPT !.foo = bar ] is the record f except for that the key foo is equal to bar.

_fail_ is also used to update the balanceOf variable (or not). If _fail_ is true then the transaction is void and the balances are not updated. However, if the transaction did not fail then the balanceOf variable is updated for the keys tx.sender and tx.toAddr. The syntax [f EXCEPT ![foo] = g(@)] is the function f except for that the key equal to the value of foo is equal to the value of the operator g(@), where @ is the value of of foo in f (@ can be used as a variable).

If the transaction does not fail, funds are transferred: the sender balance decreases by tx.value and the toAddr balance increases by tx.value.

### ProcessTransferFrom

_transfer_ transactions are made by addresses transferring their own funds. _transferFrom_ transactions transfer funds between any two addresses, so long as the caller of transferFrom has been give approval.

```tla
ProcessTransferFrom(tx) == 
    /\ pendingTransactions' = pendingTransactions \ { tx }
    /\ UNCHANGED nextTxId
    /\  LET fail ==
          \/ tx.value < 0
          \/ tx.value > balanceOf[tx.fromAddr]
          \/ tx.value > allowance[tx.fromAddr, tx.sender]
          \/ tx.fromAddr = tx.toAddr
        IN
        /\ lastTx' = [ tx EXCEPT !.fail = fail ]
        /\  IF fail
            THEN UNCHANGED <<balanceOf, allowance>>
            ELSE
            \* transaction succeeds
            \* update the balances of the 'fromAddr' and 'toAddr' addresses
            /\ balanceOf' = [
                    balanceOf EXCEPT
                    ![tx.fromAddr] = @ - tx.value,
                    ![tx.toAddr] = @ + tx.value
               ]
            \* decrease the allowance for the sender
            /\ allowance' = [
                    allowance EXCEPT
                    ![tx.fromAddr, tx.sender] = @ - tx.value
               ]
```

Similarly to the ProcessTransfer action, ProcessTransferFrom defines an inline _fail_ operator and uses it control the logic elsewhere in the action. In this case the transaction will fail if

- the value is negative
- the fromAddr has insufficient balance to make the transfer
- the value is greater than the amount tx.fromAddr has allowed tx.sender to spend on their behalf
- the fromAddr and toAddr are the same

If the transaction does not fail, then the balances are updated and the spending allowance is decreased.

### ProcessApprove

ProcessApprove does not transfer funds: it updates the allowance (quantity of funds) that tx.spender can spend on behalf of tx.sender.

The transaction will fail if the tx.value field is negative or if tx.sender = tx.spender.

```tla
ProcessApprove(tx) ==
    /\ pendingTransactions' = pendingTransactions \ { tx }
    /\ UNCHANGED <<balanceOf, nextTxId>>
    /\  LET fail == tx.value < 0 \/ tx.sender = tx.spender IN
        /\ lastTx' = [ tx EXCEPT !.fail = fail ]
        /\  IF fail
            THEN UNCHANGED allowance
            ELSE
            \* transaction succeeds
            \* set the allowance for the pair <<sender, spender>> to value
            allowance' = [ 
                allowance EXCEPT
                ![tx.sender, tx.spender] = tx.value 
            ]
```

## Type checking

We should run the type checker to make sure we have not made a silly mistake writing the model. The model has medium complexity and size so annotating types for the variables and the ADDRESSES operator should be enough for Apalache to be able to understand the entire model. 

```bash
java -jar apalache-pkg-0.17.5-full.jar typecheck ERC20.tla

# Apalache output:
# ...
# Type checker [OK]
```

You should see Type checker [OK].

## Finding an exploit

### Trace Invariants using Seq(STATE)

We have defined the state and the allowed transitions. It is time to explore behavior using Apalache.

Apalache lets you define [trace invariants](https://apalache.informal.systems/docs/apalache/invariants.html?highlight=invariant#trace-invariants): boolean functions over the entire sequence of states in an execution. They let you detect system behavior that single state boolean functions would not be able to detect.

A trace invariant should be an operator of the following form

```tla
\* @type: Seq(STATE) => Bool;
Foo(trace) == ...
```

In order to use trace invariants we must define a STATE type alias in typdefs.tla. The STATE type should be a record using variable names as keys, mapping to the variable type.

```tla
(*

  @typeAlias: STATE = [
    balanceOf: ADDR -> Int,
    allowance: <<ADDR, ADDR>> -> Int, 
    pendingTransactions: Set(TX),
    lastTx: TX,
    nextTxId: Int
  ];

*)
```
It is straightforward to copy the declerations following the VARIABLES keyword that we already wrote.

Given the alias, Foo allows us to access any state in the execution trace using sequence indexing (1-based). For example we can access the initial state with trace[1], the second state with trace[2] ect.

### Trace Invariant: All Fund Transfers Have Sufficient Approval

The Ethereum API has the expected behavior that if you approve a third party to make transfers from your address, then the sum of those transfers should not exceed the value that you specified.

We write a trace invariant that says

"Whenever a third party makes transfers from a given address on behalf of the owner, an _Approve_ transaction with a value not less than the sum of the transfers should have been submitted by the owner of the address, before all transfers included in the sum were made."

We can specify this criteria in TLA+

```tla
\* @type: Seq(STATE) => Bool;
AllFundTransfersHaveSufficientApproval(trace) ==
    \A spender, fromAddr \in ADDRESSES:
        LET TransferIndices == {
            i \in DOMAIN trace:
                LET tx == trace[i].lastTx IN
                /\ tx.tag = "transferFrom"
                /\ ~tx.fail
                /\ tx.fromAddr = fromAddr
                /\ tx.sender = spender
                /\ 0 < tx.value
        }
        IN
        \* the sum of all transfers from 'fromAddr' to 'toAddr'
        LET SumOfTransfers ==
            LET Add(sum, i) == sum + trace[i].lastTx.value IN
            FoldSet(Add, 0, TransferIndices)
        IN
        \* there exists an approval for the whole transfer sum
        LET ExistsApprovalForSumInPast ==
          \E i \in DOMAIN trace:
            LET approval_tx == trace[i].lastTx IN
            /\ approval_tx.tag = "approve"
            /\ spender = approval_tx.spender
            /\ fromAddr = approval_tx.sender
            \* all transfers are made after the approval
            /\ \A j \in TransferIndices: i < j
            /\ ~approval_tx.fail
            \* the sender of this transaction is allowing the spender
            \* to spend at most the sum of the made transfers.
            /\ SumOfTransfers <= approval_tx.value
        IN
        SumOfTransfers <= 0 \/ ExistsApprovalForSumInPast
```

There are a few things going on here.

First of all we must check the condition for all pairs of addresses

```tla
\A spender, fromAddr \in ADDRESSES:
    ...
```

For each pair we define an inline operator TransferIndices, the set of indexes into the sequence of states in which a transfer was made by `spender` from `fromAddr` to another address.

```tla
LET TransferIndices == {
        i \in DOMAIN trace:
            LET tx == trace[i].lastTx IN
            /\ tx.tag = "transferFrom"
            /\ ~tx.fail
            /\ tx.fromAddr = fromAddr
            /\ tx.sender = spender
            /\ 0 < tx.value
    }
```

We can collect the sum of these transfers by using the FoldSet operator included in the [Apalache library module](https://github.com/informalsystems/apalache/blob/unstable/src/tla/Apalache.tla) (EXTENDS Apalache).

```tla
LET SumOfTransfers ==
    LET Add(sum, i) == sum + trace[i].lastTx.value IN
    FoldSet(Add, 0, TransferIndices)
```

The [FoldSet](https://github.com/informalsystems/apalache/blob/2b736c9ffd874d583de0c1e57ecd100bc251b517/src/tla/Apalache.tla#L78) operator is one of the most useful reusable operators available. The form is  

```tla
FoldSet(Combiner, initialValue, inputSet)
```

where Combiner is an operator 

```tla
Combiner(accumulatedValue, nextValue)
```

The value of a FoldSet call is the result of repeatedly applying Combiner to successive elements in inputSet (in unpredictable order) as well as the value accumulated so far in the process.

Our usage SumOfTransfers sums the .value field of the lastTx variable for each state indexed by TransferIndices.

```tla
LET SumOfTransfers ==
    LET Add(sum, i) == sum + trace[i].lastTx.value IN
    FoldSet(Add, 0, TransferIndices)
```

A last component of our trace operator is ExistsApprovalForSumInPast

```tla
    LET ExistsApprovalForSumInPast ==
        \E i \in DOMAIN trace:
        LET approval_tx == trace[i].lastTx IN
        /\ approval_tx.tag = "approve"
        /\ spender = approval_tx.spender
        /\ fromAddr = approval_tx.sender
        \* all transfers are made after the approval
        /\ \A j \in TransferIndices: i < j
        /\ ~approval_tx.fail
        \* the sender of this transaction is allowing the spender
        \* to spend at most the sum of the made transfers.
        /\ SumOfTransfers <= approval_tx.value
```

The operator will evaluate true if there exists an approval in the transaction history that precedes each transfer, and the approval value was not less than the sum of total transfers.

Finally, we can put the pieces together.

```tla
AllFundTransfersHaveSufficientApproval(trace) ==
    \A spender, fromAddr \in ADDRESSES:
        \* ...
        IN
        SumOfTransfers <= 0 \/ ExistsApprovalForSumInPast
```

The final value of AllFundTransfersHaveSufficientApproval will be _false_ if and only if there is a pair of addresses with a positive SumOfTransfers and no approval for those transfers was made.

Check the invariant

```bash
java -jar apalache-pkg-0.17.5-full.jar check --inv=AllFundTransfersHaveSufficientApproval ERC20.tla

# Apalache output:
# ...
# State 8: Checking 1 trace invariant(s)                            
# State 8: trace invariant 0 violated. Check the counterexample in: ...
# Found 1 error(s)
```

An error!

## Interpreting an Apalache counterexample

We should check the counterexample1.tla file (located in the _apalache-out) directory. It should contain a sequence of states similar to the following (but may not be identical)

```tla
(* Initial state *)
State0 ==
  allowance
      = (((((((<<"addr1", "addr1">> :> 0 @@ <<"addr2", "addr1">> :> 0)
                    @@ <<"addr3", "addr1">> :> 0)
                  @@ <<"addr1", "addr2">> :> 0)
                @@ <<"addr2", "addr2">> :> 0)
              @@ <<"addr3", "addr2">> :> 0)
            @@ <<"addr1", "addr3">> :> 0)
          @@ <<"addr2", "addr3">> :> 0)
        @@ <<"addr3", "addr3">> :> 0
    /\ balanceOf = ("addr1" :> 28 @@ "addr2" :> 14) @@ "addr3" :> 20
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 0
    /\ pendingTransactions = {}

(* Transition 2 to State1 *)
State1 ==
  allowance
      = (((((((<<"addr1", "addr1">> :> 0 @@ <<"addr2", "addr1">> :> 0)
                    @@ <<"addr3", "addr1">> :> 0)
                  @@ <<"addr1", "addr2">> :> 0)
                @@ <<"addr2", "addr2">> :> 0)
              @@ <<"addr3", "addr2">> :> 0)
            @@ <<"addr1", "addr3">> :> 0)
          @@ <<"addr2", "addr3">> :> 0)
        @@ <<"addr3", "addr3">> :> 0
    /\ balanceOf = ("addr1" :> 28 @@ "addr2" :> 14) @@ "addr3" :> 20
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 1
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 0,
        sender |-> "addr1",
        spender |-> "addr3",
        tag |-> "approve",
        value |-> 16]}

(* Transition 1 to State2 *)
State2 ==
  allowance
      = (((((((<<"addr1", "addr2">> :> 0 @@ <<"addr3", "addr1">> :> 0)
                    @@ <<"addr2", "addr3">> :> 0)
                  @@ <<"addr3", "addr3">> :> 0)
                @@ <<"addr1", "addr3">> :> 0)
              @@ <<"addr2", "addr1">> :> 0)
            @@ <<"addr3", "addr2">> :> 0)
          @@ <<"addr1", "addr1">> :> 0)
        @@ <<"addr2", "addr2">> :> 0
    /\ balanceOf = ("addr1" :> 28 @@ "addr2" :> 14) @@ "addr3" :> 20
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 2
    /\ pendingTransactions
      = { [fail |-> FALSE,
          fromAddr |-> "addr1",
          id |-> 1,
          sender |-> "addr3",
          tag |-> "transferFrom",
          toAddr |-> "addr2",
          value |-> 6],
        [fail |-> FALSE,
          id |-> 0,
          sender |-> "addr1",
          spender |-> "addr3",
          tag |-> "approve",
          value |-> 16] }

(* Transition 3 to State3 *)
State3 ==
  allowance
      = (((((((<<"addr3", "addr2">> :> 0 @@ <<"addr2", "addr1">> :> 0)
                    @@ <<"addr3", "addr1">> :> 0)
                  @@ <<"addr3", "addr3">> :> 0)
                @@ <<"addr1", "addr1">> :> 0)
              @@ <<"addr1", "addr3">> :> 16)
            @@ <<"addr2", "addr2">> :> 0)
          @@ <<"addr2", "addr3">> :> 0)
        @@ <<"addr1", "addr2">> :> 0
    /\ balanceOf = ("addr1" :> 28 @@ "addr2" :> 14) @@ "addr3" :> 20
    /\ lastTx
      = [fail |-> FALSE,
        id |-> 0,
        sender |-> "addr1",
        spender |-> "addr3",
        tag |-> "approve",
        value |-> 16]
    /\ nextTxId = 2
    /\ pendingTransactions
      = {[fail |-> FALSE,
        fromAddr |-> "addr1",
        id |-> 1,
        sender |-> "addr3",
        tag |-> "transferFrom",
        toAddr |-> "addr2",
        value |-> 6]}

(* Transition 6 to State4 *)
State4 ==
  allowance
      = (((((((<<"addr1", "addr2">> :> 0 @@ <<"addr3", "addr1">> :> 0)
                    @@ <<"addr3", "addr2">> :> 0)
                  @@ <<"addr2", "addr1">> :> 0)
                @@ <<"addr1", "addr3">> :> 10)
              @@ <<"addr1", "addr1">> :> 0)
            @@ <<"addr2", "addr2">> :> 0)
          @@ <<"addr2", "addr3">> :> 0)
        @@ <<"addr3", "addr3">> :> 0
    /\ balanceOf = ("addr1" :> 22 @@ "addr2" :> 20) @@ "addr3" :> 20
    /\ lastTx
      = [fail |-> FALSE,
        fromAddr |-> "addr1",
        id |-> 1,
        sender |-> "addr3",
        tag |-> "transferFrom",
        toAddr |-> "addr2",
        value |-> 6]
    /\ nextTxId = 2
    /\ pendingTransactions = {}

(* Transition 2 to State5 *)
State5 ==
  allowance
      = (((((((<<"addr3", "addr2">> :> 0 @@ <<"addr2", "addr3">> :> 0)
                    @@ <<"addr2", "addr1">> :> 0)
                  @@ <<"addr2", "addr2">> :> 0)
                @@ <<"addr1", "addr3">> :> 10)
              @@ <<"addr1", "addr2">> :> 0)
            @@ <<"addr3", "addr3">> :> 0)
          @@ <<"addr1", "addr1">> :> 0)
        @@ <<"addr3", "addr1">> :> 0
    /\ balanceOf = ("addr1" :> 22 @@ "addr2" :> 20) @@ "addr3" :> 20
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 3
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 2,
        sender |-> "addr1",
        spender |-> "addr3",
        tag |-> "approve",
        value |-> 24]}

(* Transition 1 to State6 *)
State6 ==
  allowance
      = (((((((<<"addr1", "addr2">> :> 0 @@ <<"addr3", "addr1">> :> 0)
                    @@ <<"addr3", "addr3">> :> 0)
                  @@ <<"addr1", "addr3">> :> 10)
                @@ <<"addr2", "addr3">> :> 0)
              @@ <<"addr3", "addr2">> :> 0)
            @@ <<"addr2", "addr1">> :> 0)
          @@ <<"addr1", "addr1">> :> 0)
        @@ <<"addr2", "addr2">> :> 0
    /\ balanceOf = ("addr1" :> 22 @@ "addr2" :> 20) @@ "addr3" :> 20
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 4
    /\ pendingTransactions
      = { [fail |-> FALSE,
          fromAddr |-> "addr1",
          id |-> 3,
          sender |-> "addr3",
          tag |-> "transferFrom",
          toAddr |-> "addr2",
          value |-> 20],
        [fail |-> FALSE,
          id |-> 2,
          sender |-> "addr1",
          spender |-> "addr3",
          tag |-> "approve",
          value |-> 24] }

(* Transition 3 to State7 *)
State7 ==
  allowance
      = (((((((<<"addr3", "addr1">> :> 0 @@ <<"addr1", "addr1">> :> 0)
                    @@ <<"addr2", "addr2">> :> 0)
                  @@ <<"addr2", "addr1">> :> 0)
                @@ <<"addr2", "addr3">> :> 0)
              @@ <<"addr3", "addr3">> :> 0)
            @@ <<"addr1", "addr3">> :> 24)
          @@ <<"addr1", "addr2">> :> 0)
        @@ <<"addr3", "addr2">> :> 0
    /\ balanceOf = ("addr1" :> 22 @@ "addr2" :> 20) @@ "addr3" :> 20
    /\ lastTx
      = [fail |-> FALSE,
        id |-> 2,
        sender |-> "addr1",
        spender |-> "addr3",
        tag |-> "approve",
        value |-> 24]
    /\ nextTxId = 4
    /\ pendingTransactions
      = {[fail |-> FALSE,
        fromAddr |-> "addr1",
        id |-> 3,
        sender |-> "addr3",
        tag |-> "transferFrom",
        toAddr |-> "addr2",
        value |-> 20]}

(* Transition 6 to State8 *)
State8 ==
  allowance
      = (((((((<<"addr2", "addr1">> :> 0 @@ <<"addr3", "addr3">> :> 0)
                    @@ <<"addr3", "addr2">> :> 0)
                  @@ <<"addr2", "addr3">> :> 0)
                @@ <<"addr1", "addr3">> :> 4)
              @@ <<"addr1", "addr2">> :> 0)
            @@ <<"addr2", "addr2">> :> 0)
          @@ <<"addr3", "addr1">> :> 0)
        @@ <<"addr1", "addr1">> :> 0
    /\ balanceOf = ("addr1" :> 2 @@ "addr2" :> 40) @@ "addr3" :> 20
    /\ lastTx
      = [fail |-> FALSE,
        fromAddr |-> "addr1",
        id |-> 3,
        sender |-> "addr3",
        tag |-> "transferFrom",
        toAddr |-> "addr2",
        value |-> 20]
    /\ nextTxId = 4
    /\ pendingTransactions = {}
```

For brevity here is a cleaned up summary:

```
# State 0 (Init)
    balances = [28, 14, 20]

# State 1 - an approval is submitted.
    balances = [28, 14, 20]
    pending = {
        addr1 approve addr3 for value 16
    }

# State 2 - a transferFrom is submitted.
    balances = [28, 14, 20]
    pending = {
        addr1 approve addr3 with value 16
        addr3 transfer 6 from addr1 to addr2
    }

# State 3 - the approval is processed.
    allowances = {
        addr1 approve addr3 with value 16
    }
    balances = [28, 14, 20]
    pending = {
        addr3 transfer 6 from addr1 to addr2
    }

# State 4 - the transferFrom is processed.
    allowances = {
        addr1 approve addr3 with value 10
    }
    balances = [22, 20, 20]

# State 5 - an approval is submitted.
    allowances = {
        addr1 approve addr3 with value 10
    }
    balances = [22, 20, 20]
    pending = {
        addr1 approve addr3 with value 24
    }

# State 6 - a transferFrom is submitted.
    allowances = {
        addr1 approve addr3 with value 10
    }
    balances = [22, 20, 20]
    pending = {
        addr1 approve addr3 with value 24
        addr3 transfer 20 from addr1 to addr2
    }

# State 7 - the approval is processed.
    allowances = {
        addr1 approve addr3 with value 24
    }
    balances = [22, 20, 20]
    pending = {
        addr3 transfer 20 from addr1 to addr2
    }

# State 8 - the transferFrom is processed.
    allowances = {
        addr1 approve addr3 with value 4
    }
    balances = [2, 40, 20]
```

The problem is that addr1 made two approvals for addr3 to transfer its funds

1. approved transferring up to 16
2. approved transferring up to 24

But addr3 made two transferFroms from addr1 to addr2

1. transfer 6
2. transfer 20

Both transfers succeeded with a sum of 26, however, the intention of addr1 was to approve a lifetime maximum transfer of 16, and then increase it to 24. The problem is that the first transfer happened in between the first and second approvals. The second approval _overwrote_ the original value, not taking into account the transfer made in the meantime. This enabled a second transfer to withdraw too much.

## Wrapping up

### This tutorial

1. Described the problem being modeled
2. How to declare appropriate state variables using advanced data types
3. How to define appropriate initial states in Init
4. How to define appropriate transitions using actions in Next
5. Type checked the model
6. Writing a trace invariant - including using FoldSet
7. Analysed a counterexample.tla file that Apalache generated, showing a flaw in the API

Try the next one :)

### Further resources

- [Description of attack scenario](https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/). Written by Mikhail Vladimirov and Dmitry Khovratovich.
- [Relevant Ethereum API](https://eips.ethereum.org/EIPS/eip-20)
- [Apalache library module](https://github.com/informalsystems/apalache/blob/unstable/src/tla/Apalache.tla)
- [Apalache trace invariants](https://apalache.informal.systems/docs/apalache/invariants.html?highlight=trace%20invariant#trace-invariants)