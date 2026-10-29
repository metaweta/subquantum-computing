# Lean 4 formalization

This directory contains a Lean 4 + mathlib formalization of the
**logical/arithmetic skeleton** of the manuscript's main theorem. The
physical content enters as hypotheses rather than being proved from first
principles.

## What is formalized

- `Subquantum.Entropy` — `pStar n = (2^n)⁻¹` and the closed-form
  `R n = n · log 2 + log 4` for the nonequilibrium relative-entropy cost
  (manuscript abstract and Eq. (eq:linearresource)).
- `Subquantum.Concatenation` — the master inequality
  `q (j+1) ≤ A · q(j)² ⟹ q k ≤ A⁻¹ · (A · q 0) ^ (2^k)`
  by induction on `k` (Eq. (eq:doubleexp)).
- `Subquantum.KL` — expansion of binary KL divergence `d(c ‖ p_*)`
  isolating the `c · n · log 2` term underwriting the `Ω(n)` lower bound.
- `Subquantum.ErrorTransparent` — the operator-algebraic derivations of
  the error-transparent interface (Section 6):
  - `logicalMarker_intertwine`: from Knill–Laflamme orthogonality
    `V_b† · V_a = δ_{ab} P_C` and `Q_L · P_C = Q_L`, derives Eq.
    (eq:intertwine): `Q̃_L · V_a = V_a · Q_L`.
  - `pow_mul_of_intertwine` and `transparent_pow`: the polynomial
    content of Eq. (eq:transparentidentity),
    `(Q̃_L · p_y)^n · V_a = V_a · (Q_L · p_y)^n` for every `n`, by
    induction. The exponential form `exp(z Q̃_L p_y) · V_a =
    V_a · exp(z Q_L p_y)` follows by pulling the right-multiplication
    through the exponential's `tsum`; that normed-algebra step is left
    to future work.
- `Subquantum.FaultTolerance` — the arithmetic core of the
  Fault-tolerance theorem (Section 7):
  - `failureUpperBound_le_delta`: given the concatenation recursion
    (A3) and a level `k` satisfying the sufficient-level inequality
    `(n · log 2 + log(4L/(Aδ))) / (-log(A·q₀)) ≤ 2^k` (Eq. (eq:kbound)),
    the failure upper bound `4 · L · q(k) / p_*` is at most `δ`
    (combines (eq:neqbad), (eq:doubleexp), and (eq:kbound)).
  - `main_fault_tolerance`: existence of a concatenation level `k` at
    which the failure upper bound is at most `δ`, under the premises
    (A3-style recursion, positive constants, below-threshold condition).

## What is NOT formalized

The physical content underpinning the manuscript's theorem is not
formalized and enters `FaultTolerance.lean` only as hypotheses:

- **Basin conditioning / likelihood-ratio bound** `ρ/μ ≤ 4/p_*`
  (manuscript Eqs. (eq:fullconditioned), (eq:ratioBound)): the
  one-dimensional pilot-wave transport of the Radon–Nikodym derivative is
  not formalized. The failure upper bound `4 L q_k / p_*` is used as a
  definition rather than derived from the measure-theoretic argument.
- **Union bound (A4)** `Pr_μ(B_k) ≤ L(n) · q_k`: representing fault
  events as macroscopic configuration-space records with equilibrium
  measures equal to Born probabilities is axiomatic input.
- **Exponential form of (eq:transparentidentity)**:
  `exp(z Q̃_L p_y) · V_a = V_a · exp(z Q_L p_y)`. The polynomial content
  is proved (see `Subquantum.ErrorTransparent`), but promoting it to
  the exponential form requires a normed-algebra setting and continuity
  of right-multiplication through a `tsum`, which is not formalized here.
  The **syndrome-only transparency class** (Eq. (eq:syndromeonly)) is also
  not formalized.
- **Pilot-wave dynamics** in 1D and the cumulative-Born-probability
  conservation along trajectories.
- **Monotonicity lift** from `d(c ‖ p)` to `d(r ‖ p)` on `r ∈ [c, 1]`.
- **Polynomial `L(n)`** and the derivation that `k = O(log n)` follows
  from the sufficient-level inequality: the file provides existence of
  *some* sufficient `k`, not the explicit `O(log n)` bound on its size.

Each of these would be a substantial Lean project on its own; several
require infrastructure (quantum circuits, Bohmian trajectories, syndrome
subspaces) that is not currently in mathlib.

## Build

Install [`elan`](https://github.com/leanprover/elan). Then, from this
directory:

```bash
lake update          # fetch mathlib (may rewrite lean-toolchain)
lake exe cache get   # pull mathlib's precompiled .olean cache
lake build
```

## Status

Verified: `lake build` succeeds against Lean `v4.36.0-rc2` and current
mathlib `master` (6338 jobs, exit 0). Remaining diagnostics are advisory
mathlib `module`-system warnings only — no errors.
