# Typing the specification and checking it

## Inspecting a complete spec

1. Read [EIP-20](https://eips.ethereum.org/EIPS/eip-20)
   and try to figure how it is working.
1. Read the description of the
   [attack scenario on EIP-20](https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/)
1. Open [ERC20.tla](../examples/erc20-approve-attack/ERC20.tla)
   and [MC_ERC20.tla](../examples/erc20-approve-attack/MC_ERC20.tla).
1. Check the trace invariant `NoTransferAboveApproved`:

    ```sh
    $ apalache-mc check --inv=NoTransferAboveApproved MC_ERC20.tla
    ```
1. The tool reports an invariant violation.
1. Open the counterexample and see,
   whether it matches the above attack scenario.

