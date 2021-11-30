---
title: Modelator
description: Tool to model based testing from Informal Systems
layout: default
parent: Model Based Testing
nav_order: 3
---

[Modelator](https://github.com/informalsystems/modelator) is a tool that facilitates generation and execution of tests. Besides other features, it provides:
 - easy selection of a model checker to execute (Apalache or TLC)
 - automatic enumeration of tests in TLA+ files
 - generation of multiple test executions from the same test assertion
 - interfaces for execution of generated tests in target languages (currently Rust and Go)