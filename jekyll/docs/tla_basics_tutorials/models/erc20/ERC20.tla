----------------------------- MODULE ERC20 ------------------------------------
(*
 * Modeling ERC20 tokens of Ethereum and the Approve-TransferFrom Attack:
 *
 * EIP-20: https://eips.ethereum.org/EIPS/eip-20
 *
 * Attack scenario:
 * https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/edit#
 *
 * This TLA+ specification is designed for model checking with Apalache.
 * We do not model 256-bit integers here, as we are not interested in overflows.
 * 
 * Igor Konnov, 2021
 *)
EXTENDS Integers, Apalache, typedefs

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

\* @type: () => Set(ADDR);
ADDRESSES == { "addr1", "addr2", "addr3" }

Init ==
    \* every address has a non-negative number of tokens
    /\ balanceOf \in [ADDRESSES -> Nat]
    \* no account is allowed to withdraw from another account
    /\ allowance = [ pair \in ADDRESSES \X ADDRESSES |-> 0 ]
    \* no pending transactions
    /\ pendingTransactions = {}
    /\ nextTxId = 0
    /\ lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]

(*
Submit a transaction to the pendingTransactions pool.
*)
SubmitTx(tx) == 
    /\ pendingTransactions' = pendingTransactions \union { tx }
    /\ lastTx' = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
    /\ nextTxId' = nextTxId + 1
    /\ UNCHANGED <<balanceOf, allowance>>

(* EIP-20:
The following action submits a transaction to the blockchain.

Transfers _value amount of tokens to address _toAddr, and MUST fire the Transfer
event. The function SHOULD throw if the message caller’s account balance does
not have enough tokens to spend.

Note Transfers of 0 values MUST be treated as normal transfers and fire the
Transfer event.
*)
SubmitTransfer(_sender, _toAddr, _value) == 
    SubmitTx([  
                id |-> nextTxId,
                tag |-> "transfer",
                fail |-> FALSE,
                sender |-> _sender,
                toAddr |-> _toAddr,
                value |-> _value
            ])

(* EIP-20:
Transfers _value amount of tokens from address _fromAddr to address _toAddr, and
MUST fire the Transfer event.

The transferFrom method is used for a withdraw workflow, allowing contracts to
transfer tokens on your behalf. This can be used for example to allow a
contract to transfer tokens on your behalf and/or to charge fees in
sub-currencies. The function SHOULD throw unless the _fromAddr account has
deliberately authorized the sender of the message via some mechanism.

Note Transfers of 0 values MUST be treated as normal transfers and fire the
Transfer event.
*)
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

(* EIP-20:
Allows _spender to withdraw from your account multiple times, up to the _value
amount. If this function is called again it overwrites the current allowance
with _value.
*)
SubmitApprove(_sender, _spender, _value) == 
    SubmitTx([
                id |-> nextTxId,
                tag |-> "approve",
                fail |-> FALSE,
                sender |-> _sender,
                spender |-> _spender,
                value |-> _value
            ])

(*
 Process a Transfer transaction that was submitted with SubmitTransfer.
 *)
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

(*
 Process a TranferFrom transaction that was submitted with SubmitTransferFrom.
 *)
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

\* Process an Approve transaction that was submitted with SubmitApprove.
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

(* Expected properties *)

\* A trace invariant: For every pair <<spender, fromAddr>>, the sum of transfers
\* via TransferFrom is no greater than the maximum allowance.
\* It is quite hard to formulate this property, as there are scenarios,
\* where this behavior is actually expected.
\* In pure TLA+, we would have to write a temporal property.
\* In Apalache, we are just writing a trace invariant.
\*
\* This property is known to be violated:
\* https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/edit#
\* 
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

===============================================================================
