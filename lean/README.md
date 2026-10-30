# Lean 4 formalization

This directory contains a Lean 4 + mathlib formalization of the
logical, algebraic, and arithmetic skeleton of the manuscript. Physical
content enters as hypotheses rather than being proved from first
principles.

## Mapping to manuscript (v0.2, "Robustness transfer and conditional
## fault tolerance")

- `Subquantum.Entropy` — `pStar n = (2^n)⁻¹` and
  `R n = n · log 2 + log 4` for the nonequilibrium relative-entropy
  cost (manuscript abstract and Eq. (eq:linearresource)).
- `Subquantum.KL` — expansion of binary KL divergence `d(c ‖ p_*)`
  isolating the `c · n · log 2` term that gives the `Ω(n)` lower bound
  of Lemma 1 (Rare-set lower bound).
- `Subquantum.ErrorTransparent` — operator-algebraic content of
  Section 5:
  - `logicalMarker_intertwine`: Eq. (eq:intertwine)
    `Q̃_L · V_a = V_a · Q_L`, derived from Knill–Laflamme
    (eq:KLorthogonal) + `Q_L · P_C = Q_L`.
  - `pow_mul_of_intertwine` / `transparent_pow`: polynomial content of
    Eq. (eq:transparentidentity),
    `(Q̃_L · p_y)^n · V_a = V_a · (Q_L · p_y)^n`, by induction.
- `Subquantum.ExpTransparent` — exponential form of
  Eq. (eq:transparentidentity):
  - `exp_mul_of_intertwine`: `exp(X · p) · V = V · exp(Y · p)` from
    intertwining + commutation, by applying the exponential power
    series term-by-term via `HasSum.mul_right`/`HasSum.mul_left` in a
    complete normed ℝ-algebra.
- `Subquantum.SyndromeOnly` — syndrome-only transparency class of
  Eq. (eq:syndromeonly):
  - `commute_of_syndromeOnly_codeOnly`: in `H₁ ⊗ H₂`, operators of
    form `id ⊗ s` commute with operators of form `Q ⊗ id`.
  - `commute_of_transparent_encoded`: pulled back through an isometry
    `W : K ≃ₗ[𝕜] H₁ ⊗ H₂`, any `S` with `WSW† = I_L ⊗ s` commutes with
    any `T` with `WTW† = Q_L ⊗ I_syn` on `K`.
- `Subquantum.MeasureBound` — the pilot-wave Radon–Nikodym transport
  underlying Section 6 (Lemma 2, Event-bound transport, and
  Theorem 1, Robustness transfer):
  - `event_bound_of_rnDeriv_le` is the content of Lemma 2
    (`lem:eventtransport`): from `ρ ≪ μ` and the pointwise bound
    `rnDeriv ρ μ ≤ C` (μ-a.e.), the event-level bound
    `ρ(E) ≤ C · μ(E)` follows by `∫_E (rnDeriv) dμ ≤ ∫_E C dμ`. This
    is the step from pointwise ratio transport along Bohmian
    trajectories to Eq. (eq:eventBound) at the event level, used in
    the proof of Theorem 1 (`thm:transfer`) with `C = 4/p_*`.
  - `failure_bound_measure_theoretic` / `failure_bound_uniform` /
    `failure_bound_from_rnDeriv` are additional lemmas that compose
    the event bound with a classical union bound over fault events.
    These are *not* used by Theorem 1 directly (the transfer
    principle delegates all fault-path bookkeeping to the
    conventional FT input `ε_k(n) ≤ L(n) q_k`, Eq. (eq:FTinput)); they
    remain available for anyone who prefers the explicit
    enumeration form.
- `Subquantum.Concatenation` — iteration of Eq. (eq:FTinput):
  - `concatenation_bound`: the master inequality
    `q(j+1) ≤ A · q(j)² ⟹ q(k) ≤ A⁻¹ · (A · q₀)^(2^k)`, by induction.
    This is the double-exponential suppression used in the proof of
    Corollary 1 (Conditional fault-tolerance scaling).
- `Subquantum.FaultTolerance` — arithmetic core of Corollary 1
  (`cor:FT`):
  - `failureUpperBound_le_delta`: given the recursion from
    Eq. (eq:FTinput) and a concatenation level `k` satisfying
    Eq. (eq:kbound), the bound `4 · L · q(k) / p_* ≤ δ` holds.
    Together with Theorem 1 this gives the nonequilibrium failure
    bound of Eq. (eq:neqbad).
  - `main_fault_tolerance`: existence of such a `k` for every
    `δ, n`. The explicit `k = O(log n)` statement of the manuscript
    is not strengthened; existence of a sufficient `k` is proved
    directly.

## What is NOT formalized

The physical content underpinning the manuscript's theorems remains
hypothesis-level:

- Common Bohmian transport of `ρ_t` and `μ_t` under the pilot-wave
  flow is used as a hypothesis of Lemma 2 and the pointwise density
  bound of Eq. (eq:ratioBound). The pilot-wave dynamics itself is
  not formalized.
- The conventional fault-tolerance input of Eq. (eq:FTinput) — the
  recursion `q_{j+1} ≤ A q_j²` and the Born-rule failure bound
  `ε_k(n) ≤ L(n) q_k` — is axiomatic input to Corollary 1. It is
  justified in the manuscript by citing Aliferis–Gottesman–Preskill,
  not derived in Lean.
- Monotonicity lift from `d(c ‖ p)` to `d(r ‖ p)` on `r ∈ [c, 1]`,
  used in the proof of Lemma 1.
- The architectural requirements highlighted in the manuscript's
  Section 7 — logical opacity of ordinary equilibrium records,
  bounded-body implementation of the error-transparent readout,
  direct control of large pointer disturbances — are open problems
  in the manuscript and not addressed here.

The scope statement from Lemma 2 and Theorem 1 of the manuscript is
exactly what the Lean development proves: given common Bohmian
transport (a physical hypothesis) and a conventional Born-rule failure
bound (an architectural hypothesis), the nonequilibrium failure bound
`4 ε / p_*` follows mechanically, as does its concatenated-code
corollary.

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
