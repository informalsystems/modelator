---
title: (Bonus) Ecosystem
description: A glance at the TLA+ ecosystem
layout: default
parent: TLA+ Basics Tutorials
nav_order: 8
---

# The TLA+ ecosystem

There are a number of resources in the ecosystem. The most important are

1. The language itself
2. [Apalache](https://github.com/informalsystems/apalache) - a symbolic bounded model checker
3. [TLC](https://github.com/tlaplus/tlaplus) - an explicit state model checker

The Apalache and TLC model checkers each have pros and cons that make them suited for evaluating different models.

There are common names you will see repeatedly as you learn TLA+. We use the following

1. [VSCode Plugin](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) - highlights and shows syntax errors, runs TLC\
We recommend using this.
2. [TLA+ standard modules](https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules) - the standard library\
These modules are automatically found by Apalache and TLC when you include them.
3. [Google Group](https://groups.google.com/g/tlaplus) - the official discussion forum for TLA+\
It's worth searching here if you're stuck.
4. [tlaplus repository issues](https://github.com/tlaplus/tlaplus/issues) - the issues for the TLA+ components maintained by Microsoft\
It's worth searching here if you're stuck.

Additional keywords you might see, but that we don't use in the basic tutorials:

1. [Modelator](https://modelator.informal.systems/) - a tool for model-based testing using TLA+ models\
modelator can generate hundreds of tests from a model and run them against your real system.
2. [SANY](https://github.com/tlaplus/tlaplus) - the canonical TLA+ parser used by TLC and Apalache\
You don't need to worry about using SANY on its own.
3. [Toolbox](https://github.com/tlaplus/tlaplus) - a bespoke IDE for writing TLA+ and running TLC.\
The toolbox has unique features useful in niche circumstances. We recommend trying the toolbox only after getting used to TLA+, if you need to.
4. [TLA+ community modules](https://github.com/tlaplus/CommunityModules) - additional modules contributed by the community\
Using them may require downloading and providing the path for the package.
5. [Pluscal](https://learntla.com/pluscal/a-simple-spec/) - another language which translates to TLA+\
Pluscal is less expressive than TLA+ and uses a different syntax. There are Pascal and C-like flavours. You have to translate it to TLA+ using a transpiler before checking a model written in it. We recommend trying it only after getting used to using regular TLA+.
6. [Specifying Systems](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf) - a book on TLA+ written by Leslie Lamport, original creator of TLA+\
It contains useful information on niche features of TLC and TLA+.

## Footnote

Please note there are many more tools and works in the ecosystem. This page contains a basic subset.