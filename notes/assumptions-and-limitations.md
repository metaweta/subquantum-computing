# Assumptions and Limitations

This note tracks the explicit scientific hypotheses used in the manuscript's main theorems. The numbering is informal and tracks the current (v0.4) manuscript.

## Resource model

The additive resource is the relative entropy `D(rho || mu)` between the actual pilot-wave ensemble and the Born equilibrium distribution. The theorem does not price the production, isolation, storage, or cosmological availability of nonequilibrium matter.

**Caveat on preparation cost.** The preparation shell `A_*` has equilibrium probability `p_*/4`, so producing one shell configuration by ordinary equilibrium rejection sampling would require an expected `4·2^n` attempts. The `n·ln 2 + O(1)` bound is a specific information-theoretic resource; it does not imply polynomial *physical* preparation cost in any particular model.

## Computational promise

The main primitive distinguishes zero witnesses from one witness. The design weight is `p_* = 2^{-n}`; the actual marked-state weight on promised inputs is `p_f` in `{0, p_*}`.

## Pointer dynamics (spinor-only hypothesis)

The pointer `y` is the sole Bohmian configuration coordinate of the model. The computational register is treated as spinor-only (internal indices only), so that `ẏ = J/P` with `J, P` the marginal current and density is the full Bohmian guidance equation rather than a reduction from a joint `(x, y)` guidance law. The cumulative-Born-probability conservation argument of Section 3 depends on this hypothesis: if the register carried additional Bohmian configuration coordinates `x`, conditioning only on a pointer interval could leave spatial sectors unchanged and break the deterministic-selection argument. The measurement displacement is chosen so that the final marked and unmarked packets are disjoint and ordered.

## Fault model (history-event realizable)

The robustness-transfer theorem (Theorem 1) and its concatenation corollary (Corollary 1) assume:

1. a complete polynomial-size encoded computation with `L(n)` logical locations;
2. a measurable *decision-fault* trajectory event `H_dec ⊆ Γ_T` with equilibrium path probability `≤ ε_dec`;
3. a measurable *record-leakage* trajectory event `H_rec ⊆ Γ_T`, defined through a stochastic fault-label map `Λ : Γ_T → Ω` and the set of labels for which the conditional record channel violates logical-value independence, with equilibrium path probability `≤ ε_rec`;
4. that every trajectory outside `H_dec ∪ H_rec` reaches readout with the correct marked/unmarked value while satisfying label-wise record independence;
5. a below-threshold distance-three recursion `q_{j+1} ≤ A·q_j²` and a conventional Born-rule failure bound `ε_dec,k + ε_rec,k ≤ L(n)·q_k`;
6. optionally, a direct nonequilibrium bound `η` on larger pointer disturbances not captured by the two events above (bounded disturbances are instead absorbed by the constant `λ·ln 2` physical margin).

The transfer theorem does **not** require a fault-pattern map or exact pattern probabilities; it needs only measurable bad-history events with the stated equilibrium bounds. A trace-distance, diamond-norm, or coherent-fault-path bound does not by itself supply history-event realizability. Extension to local non-Markovian coherent noise (as in Aliferis–Gottesman–Preskill's amplitude-level treatment) is an open problem.

## Hardware

The encoded projector is mathematically defined, but no derivation from a restricted realistic two-body hardware Hamiltonian is supplied. Known error-transparent constructions can require higher-body interactions. Fixed body-ness does not affect asymptotic complexity, but a scalable bounded-body realization that simultaneously satisfies the fault-tolerance threshold and keeps pre-readout record leakage small is an open problem, not a corollary of ordinary threshold theorems.

## Complexity consequence

The Valiant–Vazirani consequence is randomized. The promise solver may behave arbitrarily on instances with more than one witness. SAT decision follows by repeated randomized isolation and amplification in the enlarged subquantum model; witness recovery is a separate standard SAT self-reduction.
