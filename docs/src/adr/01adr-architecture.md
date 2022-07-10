# ADR-01: Modelator Architecture

| authors           | revision | revision date  |
| ----------------- | --------:| --------------:|
| Andrey Kuprianov  |        1 | July 09, 2022  |

## Motivation

Modelator, as we develop it now, is a general framework for creation of customized tools that implement different flavors of [Model-based Testing](https://en.wikipedia.org/wiki/Model-based_testing) (MBT). The tools based on Modelator can be customized in the following ways:
- **Application area**: e.g. our primary focus now is on [Cosmos](https://cosmos.network)-based blockchains, but we are considering to expanding to both other types of blockchains as well as to general software
- **Level of testing**: our current focus is on end-to-end testing, but in the near future we plan to expand to unit and integration testing
- **Modeling language**: currently we use TLA+, but plan to support more restricted, domain-specific input languages (DSLs), e.g. in the style of Behavior-driven Development (BDD) and Property-based Testing (PBT).
- **Target language**: the first target language (the language where test is being executed) is Python, but we plan to support also at least Rust and Go.

MBT is a testing method in which test traces are generated from models; so under the hood we run model checkers (MCs) such as [Apalache](https://apalache.informal.systems) and [TLC](https://github.com/tlaplus/tlaplus). In order to motivate the architectural aspects of Modelator, we compare its mode of operation with that of model checkers.

- **Users**:
  - MCs have **academic users**, as well as verification engineers from industry (thus also with academic background). They often tend to forgive some tool problems (e.g. throwing of exceptions), in case they can side-step them.
  - Modelator will have **industrial users**, who are used to tools _just working_, and are not willing to forgive even small roughness in the tool.
- **Performance** is very related to the above:
  - MCs academic users are often consent with waiting for **a few hours** to get the results.
  - Modelator industrial users are used to the tools working fast; a delay of **a few minutes** is often perceived as unacceptably slow.
- **User experience (UX)**
  - MCs are command-line tools, with relatively simple textual input (TLA+ model + invariants + constants), and textual output (no error / error + counterexample trace).
  - To satisfy user requirements wrt. ease of use and performance, Modelator needs to have rich inputs (specialized DSLs, synthesis of model parts, interactive user interface), and rich outputs (possibly dynamic test reports, with support of storage, retrieval & exploration; possibly graphical representation of results).
- **Task parallelism**:
  - MCs are **one-task programs**. A model checking task consists primarily of a model and an invariant to check. The task is executed till its completion.
  - Modelator is a **massively multi-task program**. It executes a test suite, which consists of multiple tests. A test suite can be parameterized by multiple combinations of parameters. Finally, each test can generate multiple traces, and each trace needs to be executed against a SUT. Thus we have parallelism multiplying through at least 3 layers throughout task execution.
- **Running mode**: 
  - MCs operate in **one-shot mode**: given all parameters they perform model checking, may generate (one or more) traces, and forget about them. Each new invocation is independent from the previous ones.
  - Modelator has to operate in **persistence mode**: the amount of tasks to execute is huge, and forgetting what has been done already in the previous tool invocations is not an option.
- **Execution environment**:
  - MCs operate essentially in a vacuum: they don't have any dependencies besides very basic ones (e.g. JRE).
  - Modelator, depending on its instantiation, has to inter-operate with various other libraries, frameworks, and languages:
    - it encapsulates MCs, so it transitively inherits their dependencies, plus the MCs themselves;
    - it needs to interact with target systems. If the purpose of its instantiation is, e.g. end-to-end testing, Modelator needs to instantiate the target blockchain, and communicate with it. If it is unit- or integration testing, Modelator needs to interact with the target language(s) of the system under test.

