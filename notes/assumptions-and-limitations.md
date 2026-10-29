# Assumptions and Limitations

## Resource model

The additive resource is the relative entropy `D(rho || mu)` between the actual pilot-wave ensemble and the Born equilibrium distribution. The theorem does not price the production, isolation, storage, or cosmological availability of nonequilibrium matter.

## Computational promise

The main primitive distinguishes zero witnesses from one witness. The design weight is `p_* = 2^{-n}`; the actual marked-state weight on promised inputs is `p_f` in `{0, p_*}`.

## Pointer dynamics

The pointer is one dimensional, its current vanishes at negative infinity, and the measurement displacement is chosen so that the final marked and unmarked packets are disjoint and ordered. The cumulative Born probability along a Bohmian trajectory is then conserved.

## Fault model

The fault-tolerance theorem assumes:

1. a complete polynomial-size encoded computation with `L(n)` logical locations;
2. a fixed-size error-transparent base pointer interface;
3. a specified transparent set containing the no-fault history, the proved one-qubit fault histories, and syndrome-only sequences;
4. all other histories are counted as nontransparent;
5. a below-threshold distance-three recursion `q_{j+1} <= A q_j^2`;
6. syndrome-resolved histories and logical failures correspond to macroscopic configuration-space records with ordinary Born probabilities.

The proof does not cover a general unsyndromed coherent bath with interfering fault paths.

## Hardware

The encoded projector is mathematically defined, but no derivation from a restricted realistic two-body hardware Hamiltonian is supplied. Known error-transparent constructions can require higher-body interactions. Fixed body-ness does not affect asymptotic complexity, but it is a physical implementation assumption.

## Complexity consequence

The Valiant–Vazirani consequence is randomized. The promise solver may behave arbitrarily on instances with more than one witness. SAT decision follows by repeated randomized isolation and amplification in the enlarged subquantum model; witness recovery is a separate standard SAT self-reduction.
