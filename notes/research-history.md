# Research History

The project began with Valentini’s observation that the computational power of nonequilibrium pilot-wave systems cannot be assessed without determining how nonequilibrium resources scale with problem size.

The investigation first examined direct subquantum measurements of exponentially close states and found an exponential spatial-resolution or noise issue in that architecture. It then explored regenerative nonlinear gates acting on normalized conditional branches. That line clarified how a branchwise nonlinear model could avoid analog precision but also showed that such a composition rule is an additional physical assumption not supplied by ordinary pilot-wave mechanics.

The analysis then shifted to a different pilot-wave mechanism. A reversible verifier marks a unique witness state of Born weight `2^{-n}`. A nonequilibrium pointer is prepared in the Bohmian basin of the marked outcome. In one dimension, cumulative Born probability is conserved along trajectories, allowing the basin to be described exactly. Conditioning equilibrium on a shell of probability `Theta(2^{-n})` gives a relative-entropy cost `Theta(n)`.

The noise analysis evolved through several corrections. An intermediate draft bounded failure through a fault-history enumeration; the current (v0.4) manuscript instead isolates a trajectory-space robustness-transfer theorem (Theorem 1): the pointwise Radon–Nikodym bound `dρ/dμ ≤ 4/p_*` lifts to an event-level bound on any measurable history event. Fault-tolerance (Corollary 1) then enters as a conditional input through an abstract history-event realizability property for `H_dec` and `H_rec`, with the independent-stochastic AGP regime as one sufficient realization. The record-leakage event `H_rec` is defined trajectory-wise via a measurable fault-label map and the set of labels on which the conditional record channel violates logical-value independence.

This file is a high-level development record, not a substitute for the derivations.
