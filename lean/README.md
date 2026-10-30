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
    induction.
- `Subquantum.ExpTransparent` — the exponential form of Eq.
  (eq:transparentidentity):
  - `exp_mul_of_intertwine`: `exp(X · p) · V = V · exp(Y · p)` under
    the hypotheses `X · V = V · Y` (intertwining) and `p · V = V · p`
    (pointer commutes with code-register ops). Proved by applying the
    `HasSum (fun n => (n!)⁻¹ · x^n) (exp x)` term-by-term and passing
    multiplication by `V` through via `HasSum.mul_right`/`mul_left`.
    Requires a complete normed ℝ-algebra.
- `Subquantum.MeasureBound` — the measure-theoretic content of (A4) +
  Eq. (eq:ratioBound):
  - `event_bound_of_rnDeriv_le`: from a *pointwise* density bound
    `rnDeriv ρ μ ≤ C` (μ-a.e.) and absolute continuity `ρ ≪ μ`, derives
    the *event-level* bound `ρ(E) ≤ C · μ(E)` for every set `E`. This
    is the step from the manuscript's "the ratio ρ/|Ψ|² is transported
    unchanged" (pointwise statement) to Eq. (eq:eventBound)
    `Pr_ρ(B) ≤ (4/p_*) · Pr_μ(B)`. Pure Radon–Nikodym integration.
  - `failure_bound_measure_theoretic`: in an abstract measurable space
    `Ω` with equilibrium measure `μ` and nonequilibrium measure `ρ`
    satisfying the event-level density bound `ρ(E) ≤ C · μ(E)`, and
    fault events `B : Fin L → Set Ω` covering a failure set
    `F ⊆ ⋃ᵢ Bᵢ`, we have `ρ(F) ≤ C · Σᵢ μ(Bᵢ)`. Specializing to
    `C = 4/p_*` and uniform `μ(Bᵢ) ≤ q_k` recovers Eq. (eq:neqbad).
  - `failure_bound_uniform`: uniform version `ρ(F) ≤ C · L · q`.
  - `failure_bound_from_rnDeriv`: end-to-end composition — a pointwise
    density bound + measurable fault events ⟹ union-bounded failure
    estimate (manuscript's chain (eq:ratioBound) + (eq:union)
    ⟹ (eq:neqbad)).
  - What this does **not** do: justify that the pilot-wave flow
    actually preserves the pointwise density bound (that is the
    physics content of pilot-wave Radon–Nikodym transport) or that
    fault histories admit the measurable structure (A4). What it
    isolates: exactly those two physical inputs are what the
    reviewer is being asked to grant; everything downstream is
    measure theory.
- `Subquantum.SyndromeOnly` — the syndrome-only transparency class of
  Eq. (eq:syndromeonly):
  - `commute_of_syndromeOnly_codeOnly`: in the tensor-product model
    `H₁ ⊗ H₂`, operators of form `id ⊗ s` (syndrome-only) commute with
    operators of form `Q ⊗ id` (code-only), since both compositions
    equal `Q ⊗ s`. Uses `LinearMap.lTensor_comp_rTensor` and
    `LinearMap.rTensor_comp_lTensor` from mathlib.
  - `commute_of_transparent_encoded`: pulling back through an isometry
    `W : K ≃ₗ[𝕜] H₁ ⊗ H₂`, any transparent operator (`WSW† = I_L ⊗ s`)
    commutes with any encoded-pointer operator (`WQ̃_LW† = Q_L ⊗ I_syn`)
    on the full physical space `K`. This is the manuscript's statement
    in Section 6.
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
mathlib `master` (6816 jobs, exit 0). Remaining diagnostics are advisory
mathlib `module`-system warnings only — no errors.
