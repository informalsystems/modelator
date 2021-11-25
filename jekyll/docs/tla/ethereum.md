---
title: Ethereum
layout: default
parent: Tla+
grand_parent: Model Based Testing
---
# Finding an Ethereum exploit using Apalache

In 'Hello World' we used TLC to check a simple model. Now we will walk through a real model. The model models part of the ERC20 Ethereum blockchain technical standard; in particular the model can be used to generate a trace which exploits the API to transfer funds to an attackers address. The model was written by Igor Konnov.

## Intro

This model builds on the skills gained in 'Hello World'.

The model variables use a richer set of data structures including integers, tuples, and key value maps. The operator definitions are also more complicated, making greater use of the LET statement to define helper operators inline. 

Finally, we will search for a more interesting behavior pattern than we did in 'Hello World': an execution that withdraws funds from a target wallet into an attackers wallet. In this way we will see how TLA+ can be used to find vulnerabilities in a real system.

## The modeled system

The system being modeled is a system that maintains addresses corresponding to blockchain wallets. It is possible to transfer funds between addresses, by executing transactions on the blockchain. There is a pool which holds transactions which have been submitted for execution, but have not yet been executed; these are the pending transactions. Additionally, it is possible for wallet owners to delegate the ability to transfer their funds to a third party. This functionality is used in automated [smart contracts](https://en.wikipedia.org/wiki/Smart_contract) programs.

The Ethereum ERC20 standard defines an [API](https://eips.ethereum.org/EIPS/eip-20) for operating such a system. The API

```
alias apalache="java -jar ~/Documents/work/mbt/tla-basics-tutorial/models/apalache-pkg-0.17.4-full.jar"
apalache-mc check --inv=NoTransferAboveApproved MC_ERC20.tla
```