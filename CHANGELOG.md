# Changelog

## Unreleased

Response to external review of commit `4b8850d`:

- Manuscript: added the spinor-only (one-dimensional Bohmian configuration) hypothesis as an explicit paragraph in Section 3; without it the marginal guidance law `ẏ = J/P` does not determine the full trajectory dynamics.
- Manuscript: redefined the record-leakage history event `H_rec` trajectory-wise through a measurable fault-label map `Λ: Γ_T → Ω` and label-conditional record channels, eliminating the earlier channel-equality wording whose trajectory-level interpretation was ambiguous.
- Manuscript: added an explicit resource-model caveat after the linear-cost derivation in Section 4, noting that preparing the shell via equilibrium rejection sampling would still cost `Θ(2^n)` attempts.
- Scripts: `check_scaling.py` now carries `log_q` through to the final display step rather than exponentiating and re-logging; fixes a `math domain error` at large `n` (e.g. `n = 1000`, `k = 8`) and adds a regression test.
- CI: build-latex workflow now also runs the Python unit tests and `lake build` on the Lean formalization.
- Lean: added `main_fault_tolerance_log_bound` in `Subquantum.FaultTolerance`, an explicit `k = O(log n)` form that bounds `2^k` by an affine function of `T = (n·log 2 + log(4L/(Aδ))) / (−log(A·q0))`.
- Documentation: `AGENTS.md`, `notes/assumptions-and-limitations.md`, `notes/research-history.md`, and `lean/README.md` synchronized with manuscript v0.4 (robustness-transfer theorem, history-event realizability, spinor-only hypothesis, resource-model caveat).
- Licensing: adopted a dual license — Apache License 2.0 for code (`scripts/`, `lean/`, `Makefile`, `.github/workflows/`) and CC BY 4.0 for the manuscript and documentation prose; added `LICENSE`, `LICENSE-MANUSCRIPT`, and updated `LICENSE-STATUS.md`.

## 0.1.0 — 2026-10-29

Initial repository snapshot.

Included the revised manuscript after the following technical repairs:

- corrected the rare-set lower bound by requiring `0 < p < c <= 1` and proving monotonicity in the selected probability;
- distinguished the design value `p_* = 2^{-n}` from the actual marked-state weight `p_f`;
- defined the error-transparent logical projector on the full five-qubit Hilbert space and specified the extension for nonperfect fixed codes;
- narrowed the transparent-history claim to the proved one-fault and syndrome-only cases;
- included the complete `L(n)`-location computation in the fault-tolerance union bound;
- corrected the randomized Valiant–Vazirani consequence and separated decision from search self-reduction;
- retained explicit limitations concerning nonequilibrium preparation, microscopic baths, and hardware realization.
