# CHANGELOG

## v0.4.2

Few fixes and dependency improvements.

### RUST

- Parse ranged sets from TLA states. (#157)
- `clap` v3 (#162)

## v0.4.1

Various fixes and improvements.

### BUG FIXES

- Rust
  - Fix panics at unexpected jars. (#151)
  - Fix concurrent TLC execution. (#152)

### IMPROVEMENTS

- Go
  - Smoother Go build. (#146)
- Rust
  - Update Apalache to `v0.17.5`. (#135)

### NOTES

- Rust
  - A unique directory to store model-checker jars. (#137)

## v0.4.0

Like the last minor release, this is another massive refactoring release.
- Reworked interfaces for friendlier usage.
- Better parsers for improved handling of model checker outputs.
- Golang bindings.

### FEATURES

- Go
  - Modelator-go for Golang.
  - Implemented step runner.
- Rust
  - Event stream API.
  - Support for parallel tests.

### IMPROVEMENTS

- Rust
  - Huge rework on modelator-rs API and CLI.
  - Better parsers for TLA+ traces.
  - Execute model checkers in temporary directories to avoid clutters.

### TEST

- General
  - CI Workflow matrix for Windows, MacOS, and Linux.
- Rust
  - Large integration test.

## v0.3.2

This is a bug-fixing release:
 - fixed #112 related to clap beta release

## v0.3.0

This is the massive refactoring release: all internal and external interfaces has been changed; also the tool stability has been greatly improved.

Improvements:
 - Refactor error handling (#53)
 - Reliable extraction of counterexample traces (#58)
 - Reintroduce generic artifacts (#61)
 - Rework Apalache module (#62)
 - Rework TLC module (#63)

Bug fixes:
 - Confusing "No test trace found" error state (#52)
 - Running binary with only the argument tla causes panic instead of giving warning to user (#55)
 - Translate.tla counterexample using modelator tla tla-trace-to-json-trace <filename> results in parsing error (#56)

## v0.2.1

This is a bug-fixing release:
 - fixed #57 related to clap beta release

## v0.2.0

* provide two top-level functions to test a system using execution traces coming from TLA+ (see #44)
  - `run_tla_steps` will run anything that implements a `StepRunner` trait: this is suitable for small specs and simple cases
  - `run_tla_events` will run an implementation of `EventRunner`, which expects that a TLA+ state is structured, and contains besides state, also the `action` to execute, as well as the `actionOutcome` to expect.
* make Apalache the default model checker
* execute model checkers in a temporary directory (see #48)

## v0.1.0

This is the first public version; please use the crate at https://crates.io/crates/modelator/0.1.0

Cargo dependency: `modelator = "0.1.0"`

