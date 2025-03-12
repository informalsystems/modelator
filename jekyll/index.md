---
layout: default
title: Model Based Techniques
nav_order: 1
description: Model Based Techniques at Informal Systems
has_children: true
---

# Model Based Techniques for Software Correctness
Building a model of our software gives us a couple of elegant and efficient ways to increase confidence in its correctness.
Modeling languages (such as [TLA+](https://lamport.azurewebsites.net/tla/tla.html) and [Quint](https://github.com/informalsystems/quint)) are supported by _model checkers_, which enable us to reason about the model's properties.
We can specify desired properties and verify that the model satisfies them. We can also generate a large number of tests directly from the model and run them against the implementation.

A model can be written even before the development starts.
This enables finding problems early on, in the development phase.

Besides being a tool for finding difficult-to-spot problems, models serve as high-level yet precise and executable specifications.


# Model Based Techniques @ Informal Systems

At [Informal Systems](https://informal.systems), we use model-based techniques both in our development practice and as a part of our security audit services.
As a premier partner in protocol design and cross-chain infrastructure, we develop and maintain the following tools that make model-based techniques easy
to incorporate into the development and auditing practice:

 - [Quint](https://github.com/informalsystems/quint), a modern modeling language
 - [Apalache](https://apalache.informal.systems/), a symbolic model checker
 - [Modelator](https://github.com/informalsystems/modelator), a tool that enables automatic generation of tests from models
 - [cosmwasm-to-quint](https://github.com/informalsystems/cosmwasm-to-quint), a tool for generating Quint model stubs and accompanying tests directly from [CosmWasm](https://cosmwasm.com/) contracts

## Learn More About Informal Systems

[Informal Systems](https://informal.systems) was founded to build trust in software and monetary systems, specializing in secure, interoperable, and fault-tolerant networks.
We bring rigorous protocol design, formal verification, and a dedication to sustainability, empowering teams to create systems people can fully rely on.

Our team is growing! Check out [our careers page](https://informal.systems/careers) to join our team of engineers, researchers, and security experts.
