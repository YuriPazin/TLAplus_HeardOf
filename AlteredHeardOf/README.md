# Altered Heard-Of Model — TLA+ Framework Extension

This folder contains the TLA+ modules that extend the base Heard-Of framework to support the **Altered Heard-Of model**, which captures **value faults** (e.g., Byzantine behavior) in round-based distributed algorithms.

This extension is under development and is part of a master's thesis at PUCRS, aiming to formally specify and verify consensus algorithms under Byzantine fault models.

---

## Overview

The **Altered Heard-Of model** [[1]](#AHOarticle) generalizes the traditional Heard-Of model by not only modeling which messages are received, but also **what content is delivered**. This allows modeling faulty processes that may send corrupted or inconsistent messages, which is essential for specifying **Byzantine fault-tolerant algorithms**.

This framework maintains the modularity of the original Heard-Of approach and reuses core structures such as process rounds, local state transitions, and communication predicates.

---

## Folder Structure

* `mainByz.tla`: Main module for model checking Byzantine algorithms under the Altered Heard-Of model. It supports parameterization of algorithms and communication predicates.
* `PeaseSet.tla`: Constructs **Pease Sets**, that contains possible transmission vectors of a given predicate and algorithm. Also Defines communication and fault model predicates (e.g., `NoSplit`, `K-Byzantine`, etc.).
* `BLV.tla`: A Byzantine-tolerant voting algorithm adapted from the paper "Tolerating Permanent and Transient Value Faults" [[2]](#BLVarticle).
* `RoundStructureByz.tla`: Round-based computation structure adapted for value faults.
* `mainByz.toolbox/`: TLC configuration files for experiments related to BLV and other Byzantine algorithms.

---

## TODO List

The following tasks are planned to complete the Altered Heard-Of framework and the corresponding master's thesis:

### Framework Development

* [ ] Finalize `PeaseSet.tla`: formal definition of value-carrying HO sets.
* [ ] Complete and validate `RoundStructureByz.tla` with altered message delivery rules.
* [ ] Generalize support for multiple faulty senders and value corruption patterns.
* [ ] Integrate reusable fault predicates in `PeaseSet.tla`.

### Algorithm Specification

* [x] Specify BLV algorithm in TLA+ (`BLV.tla`)
* [ ] Verify consensus properties (Agreement, Termination) of BLV under different predicates.
* [ ] Compare BLV’s behavior with non-Byzantine algorithms (e.g., UV) under matched configurations.

### Model Checking \& Evaluation

* [ ] Design TLC models for varying numbers of processes and fault thresholds.
* [ ] Record state space sizes and checking time for BLV under multiple conditions.
* [ ] Create performance tables for inclusion in dissertation appendix.

### Documentation \& Thesis

* [ ] Write documentation for each module (header comments and inline descriptions).
* [ ] Write thesis chapter: Altered Heard-Of model theory and motivation.
* [ ] Write thesis chapter: Specification and evaluation of Byzantine-tolerant algorithms.
* [ ] Summarize performance comparison between HO and AHO models.
* [ ] Integrate figures and examples from TLC runs into thesis.

---

## References

<a name="AHOarticle"></a>[[1]](https://doi.org/10.1145/1281100.1281136) Martin Biely, Josef Widder, Bernadette Charron-Bost, Antoine Gaillard, Martin Hutle, and André Schiper. 2007. *Tolerating corrupted communication.* In Proceedings of the twenty-sixth annual ACM symposium on Principles of distributed computing

<a name="BLVarticle">[[2]](https://doi.org/10.1007/s00446-013-0199-7) Milosevic, Z., Hutle, M. \& Schiper, A. *Tolerating permanent and transient value faults.* Distrib. Comput. 27, 55–77 (2014).

---

## How to Use

To verify Byzantine-tolerant algorithms using this framework:

1. Open `mainByz.tla` in the TLA+ Toolbox.
2. Select the desired communication predicate and algorithm (e.g., `BLV`).
3. Run TLC with appropriate parameters (number of processes, fault threshold).
4. Check temporal properties such as Agreement, Validity, and Termination.

Each `.toolbox` configuration contains examples used for evaluation in the dissertation.

