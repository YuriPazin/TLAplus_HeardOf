# TLA+ Framework for Round-Based Distributed Algorithms using the Heard-Of Model

This repository contains the TLA+ source code accompanying the [article](https://doi.org/10.5753/wtf.2025.9510):

**"Um arcabouço em TLA+ para especificação e verificação de algoritmos distribuídos usando o modelo Heard-Of."**  
by *Yuri de Souza Pazin* and *Fernando Luis Dotti* – PUCRS (Brazil)

---

## About

This project implements a reusable framework in TLA+ for specifying and model checking fault-tolerant distributed algorithms. It is based on the [**Heard-Of model**](https://link.springer.com/content/pdf/10.1007/s00446-009-0084-6.pdf) [[2]](#HOarticle), which abstracts message delivery behavior to reason about consensus in a round-based distributed setting.

The abstraction provided by the Heard-Of model makes it particularly suitable for formal verification using model checking, helping mitigate state-space explosion.

---

The Heard-Of model is a distributed computing model for assisting in constructing correctness proofs regarding round-based fault-tolerant distributed consensus algorithms. The model's high level of abstraction makes it useful in model checking, as it can mitigate the state-space explosion problem often encountered in model checking distributed algorithms.

## Purpose

The main goal of this framework is to:

- Provide a **modular and reusable TLA+ framework** for defining and verifying round-based distributed algorithms;
- Support **parameterized communication predicates**, allowing different synchrony/failure models;
- Enable **automated verification** of consensus properties (Agreement, Termination, etc.) using TLC.

## Components

This repository contains:

- *HeardOf/*: folder with all the TLA+ specifications
  - *main.tla*: the core of the framework, where the algorithm and the communication predicate can be selected. It handles the next-state transitions when model checking and does not include Heard-Of sets as state variables, which improves the verification performance. (Details in the article)  
  - *HeardOf.tla*: Construction of valid Heard-Of sets from given communication predicate.
  - *RoundStructure.tla*: Round-based computation algorithm used by the Heard-Of model, handles message deliveries and state transitions based on local process functions `S` and `T`, defined by the consensus algorithm.
  - *UV.tla*: The **Uniform Voting** (from Charron-Bost and Schiper, 2009) algorithm, written in terms of the HO model.
  - *main.toolbox/*: Configuration and results of each experiment cited in the article. 
- *ArtigoFramework.pdf*: The article presenting the framework.
- *README.md*: This file.

## Included Examples

The repository also includes fully executable TLC models for:

- Verifying **Agreement** and **Termination** under various conditions of the Uniform Voting algorithm
- Reproducing results from the original literature using:
  - Different numbers of processes
  - Different predicates (e.g., `NoSplit`, `SpaceUniform`)
- Performance comparison in terms of state space size and checking time with a [similar framework](https://dl.acm.org/doi/10.1007/978-3-642-04420-5_10)


## Reference

If you use this framework in your work, please cite:

> Pazin, Y. S., & Dotti, F. L. (2025). *Um arcabouço em TLA+ para especificação e verificação de algoritmos distribuídos usando o modelo Heard-Of.* [Article](https://doi.org/10.5753/wtf.2025.9510)

- [2](<a name="HOarticle">) Charron-Bost, B., & Schiper, A. (2009). *The Heard-Of model: computing in distributed systems with benign faults.* Distributed Computing, 22(1). [https://doi.org/10.1007/s00446-009-0084-6](https://doi.org/10.1007/s00446-009-0084-6)


## Future Work

Planned extensions include:

- Support for Byzantine fault-tolerant algorithms (e.g., PBFT)
- Integration with the **Altered Heard-Of model**
- Enhanced performance analysis and optimizations




