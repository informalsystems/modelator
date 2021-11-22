* provide two top-level functions to test a system using execution traces coming from TLA+ (see #44)
  - `run_tla_steps` will run anything that implements a `StepRunner` trait: this is suitable for small specs and simple cases
  - `run_tla_events` will run an implementation of `EventRunner`, which expects that a TLA+ state is structured, and contains besides state, also the `action` to execute, as well as the `actionOutcome` to expect.
* make Apalache the default model checker
* execute model checkers in a temporary directory (see #48)
