# Linear Nonequilibrium Information and Conditional Fault Tolerance for Subquantum Search

This repository contains a research manuscript on the resource scaling of nonequilibrium de Broglie–Bohm computation. The main result is a two-part theorem: (i) selecting a marked state of Born weight `2^{-n}` costs `n·ln 2 + O(1)` nats of relative-entropy nonequilibrium, optimal up to constants, and (ii) a trajectory-space robustness-transfer principle says that for the pointer ensemble used here, any measurable Bohmian history event with equilibrium path probability `ε` has nonequilibrium path probability at most `4ε/p_*`. Together these imply that any history-event-realizable fault-tolerant implementation whose Born-rule failure obeys `poly(n)·θ^(2^k)` suffices with `k = O(log n)` concatenation levels — polylog in the state-space size.

## Status

**Research draft; not peer reviewed.**

## Main result, conditionally stated

For a zero-versus-one-witness problem on `n` bits:

- The design weight of the marked state is `p_* = 2^{-n}`.
- Conditioning a one-dimensional pilot-wave pointer on a cumulative-Born-probability shell costs `n·ln 2 + O(1)` in relative entropy (Section 4). A data-processing argument gives a matching `Ω(n)` lower bound for constant-probability selection (Lemma 1).
- Under common Bohmian transport, a pointwise Radon–Nikodym bound `dρ/dμ ≤ C` lifts to the event-level bound `ρ_t(B) ≤ C·μ_t(B)` for every later measurable event — including measurable history events on trajectory space (Lemma 2 and the history-event corollary). Applied with `C = 4/p_*`: any measurable decision-fault event (equilibrium path-probability `≤ ε_dec`) and measurable record-leakage event (`≤ ε_rec`) contribute at most `4(ε_dec + ε_rec)/p_*` to the nonequilibrium failure probability (Theorem 1).
- If a history-event-realizable fault-tolerant architecture achieves `ε_dec,k + ε_rec,k ≤ L(n)·q_k` with `q_{j+1} ≤ A·q_j²`, then `k = O(log n)` concatenation levels suffice to drive the nonequilibrium failure below any fixed `δ > 0`, with polynomial total overhead (Corollary 1).

The theorem is conditional on: (a) access to the specified nonequilibrium pointer ensemble, (b) history-event-realizability of the decision-fault and record-leakage events on Bohmian trajectory space, and (c) a conventional Born-rule failure bound of the stated form. The transfer theorem applies to the independent-stochastic fault-tolerance regime; extending it to the local non-Markovian coherent-noise setting (where ordinary FT proofs bound coherent fault-path sums rather than classical bad-history events) is an open problem. Nothing here claims that usable nonequilibrium matter exists.

A fixed-size five-qubit error-transparent construction is given in Appendix A as an illustrative sub-component, not as part of the main theorem. A scalable bounded-body implementation that simultaneously satisfies the fault-tolerance threshold and keeps pre-readout environmental record leakage small is left as an open problem.

## Lean formalization

The main measure-theoretic, arithmetic, and operator-algebraic content is machine-checked in Lean 4 + mathlib under `lean/`:

- **Lemma 1** (binary KL expansion for the lower bound).
- **Section 4** (`R = n·log 2 + log 4` closed form).
- **Lemma 2** (Radon–Nikodym event bound; pointwise `rnDeriv ρ μ ≤ C` ⟹ `ρ(E) ≤ C·μ(E)`), and its trajectory-space specialization (`lem:historyevent`).
- **Lemma 3** (constant pointer margin `λ·log 2`).
- **Corollary 1 arithmetic** (concatenation iteration `q_k ≤ A⁻¹·θ^(2^k)` and the sufficient-level inequality ⟹ failure ≤ δ).
- **Appendix A operator algebra** (intertwining identity `Q̃_L V_a = V_a Q_L` from Knill–Laflamme; polynomial and exponential forms of the transparent-identity; syndrome-only commutation with `W`-pullback).

The physical inputs enter the Lean development as hypotheses: common Bohmian trajectory transport of ρ_t and μ_t, history-event-realizability of fault events, pilot-wave trajectory dynamics itself, and the monotonicity lift from `d(c‖p)` to `d(r‖p)` on `r ∈ [c, 1]`. See `lean/README.md` for the detailed mapping between manuscript labels and Lean theorems.

## Repository layout

- `manuscript/` — LaTeX source, compiled PDF, and Springer Nature class file.
- `lean/` — Lean 4 + mathlib formalization of the measure-theoretic event bound, Corollary 1 arithmetic, Lemma 3, and the Appendix A operator-algebraic content.
- `notes/` — assumptions, terminology decisions, research history, and AI contribution statement.
- `scripts/` — small independent arithmetic checks for the asymptotic bounds.
- `.github/workflows/` — automated LaTeX build.
- `AGENTS.md` — instructions for Codex and other coding agents.

## Build

A local TeX installation with `pdflatex` is sufficient because the bibliography is embedded in the manuscript.

```bash
make pdf
```

The compiled file is written to `manuscript/manuscript.pdf`.

Run the arithmetic checks with:

```bash
python3 scripts/check_scaling.py --n 100
python3 -m unittest scripts/test_scaling.py
```

Check the Lean proofs (requires [`elan`](https://github.com/leanprover/elan)):

```bash
cd lean
lake update
lake exe cache get
lake build
```

See `lean/README.md` for the scope of what is and is not formalized.

## AI contribution

The author used OpenAI ChatGPT (GPT-5.6 Sol) extensively for exploratory derivation, intermediate constructions, and first-draft manuscript prose, and Anthropic Claude (Opus 4.7) for the robustness-transfer restructuring and the Lean 4 + Mathlib formalization. Michael A. Stay supplied the research question, introduced the branchwise nonlinear-gate idea that motivated the investigation, challenged and redirected intermediate claims, selected the scope and assumptions, and is the sole accountable author. Neither ChatGPT nor Claude is listed as an author. See `notes/ai-contribution-statement.md` for the full disclosure.

## Citation

Citation metadata is provided in `CITATION.cff`. Until a stable release is made, cite the version or commit hash used.

## Contact

Dr. Michael A. Stay  
Computer Science Department, University of Auckland  
`mike@cs.auckland.ac.nz`

## License status

No reuse license has yet been selected. Unless and until a license is added, copyright remains with Michael A. Stay and no permission to reuse is implied.
