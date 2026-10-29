# Lean 4 formalization (partial)

This directory contains a partial formalization in Lean 4 + mathlib of the
elementary arithmetic / analytic claims from the manuscript. The physics
content (Bohmian trajectories, syndrome-resolved fault histories, von
Neumann measurement coupling) is out of scope for this pass.

## What is formalized

- `Subquantum.Entropy` — `pStar n = (2^n)⁻¹` and the closed-form
  `R n = n · log 2 + log 4` for the nonequilibrium relative-entropy cost
  stated in the manuscript's abstract.
- `Subquantum.Concatenation` — the master inequality
  `q (j+1) ≤ A · q(j)² ⟹ q k ≤ A⁻¹ · (A · q 0) ^ (2^k)`
  by induction on `k` (manuscript Eq. (eq:doubleexp)).
- `Subquantum.KL` — expansion of binary KL divergence `d(c ‖ p_*)`
  isolating the `c · n · log 2` term underwriting the `Ω(n)` lower bound.

## What is NOT formalized

- Pilot-wave dynamics in 1D and cumulative-Born-probability conservation.
- The basin-conditioning Lemma giving the exact `R = log(4/p_*)` cost.
- Error-transparent logical projector / syndrome-only histories.
- Monotonicity lift from `d(c ‖ p)` to `d(r ‖ p)` for `r ∈ [c, 1]`.
- The `L(n) · q_k` union bound and the `4 L(n) q_k / p_*` likelihood step.

These involve measure theory on configuration space, operator algebra on
syndrome subspaces, and fault-model combinatorics; each would be its own
substantial Lean project.

## Build

Install [`elan`](https://github.com/leanprover/elan). Then, from this
directory:

```bash
lake update          # fetch mathlib (may rewrite lean-toolchain)
lake exe cache get   # pull mathlib's precompiled .olean cache
lake build
```

`lean-toolchain` currently pins `leanprover/lean4:v4.14.0`. `lake update`
will overwrite this to match mathlib's current pin; follow whatever
`elan` prompts.

## Status

Verified: `lake build` succeeds against Lean `v4.36.0-rc2` and current
mathlib `master` (6334 jobs, exit 0). Remaining diagnostics are advisory
mathlib `module`-system warnings only — no errors.
