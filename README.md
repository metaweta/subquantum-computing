# Linear Nonequilibrium Information for Fault-Tolerant Subquantum Search

This repository contains a research manuscript on the resource scaling of nonequilibrium de Broglie–Bohm computation. The central conditional claim is that selecting a marked state of Born weight `2^{-n}` can require only linear relative-entropy nonequilibrium, and that the stated syndrome-resolved fault model can suppress nontransparent histories with polynomial overhead.

## Status

**Research draft; not peer reviewed.**

## Main result, conditionally stated

For a zero-versus-one-witness problem on `n` bits:

- the design weight of the marked state is `p_* = 2^{-n}`;
- conditioning a one-dimensional pilot-wave pointer on a cumulative-Born-probability shell costs `n ln 2 + O(1)` in relative entropy;
- a corrected data-processing argument gives a matching linear lower bound for constant-probability selection;
- under assumptions (A1)–(A4) in the manuscript, `O(log n)` levels of concatenated fault tolerance suffice for a complete polynomial-size computation.

The theorem is explicitly conditional on access to the specified nonequilibrium ensemble, a fixed-size error-transparent interface, and syndrome-resolved fault histories represented by macroscopic configuration-space records. It is not a theorem for an arbitrary unsyndromed coherent bath, nor a claim that usable nonequilibrium matter exists.

The logical/arithmetic skeleton of the main theorem is machine-checked in Lean 4 + mathlib under `lean/`: the closed form `R = n·log 2 + log 4`, the concatenation inequality `q(j+1) ≤ A·q(j)² ⟹ q(k) ≤ A⁻¹·(A·q 0)^{2^k}`, the linear-in-n expansion of binary KL divergence `d(c ‖ p_*)`, and the implication that a concatenation level `k` satisfying the sufficient-level condition achieves `4·L·q(k)/p_* ≤ δ`. The physical premises (pilot-wave transport of the Radon–Nikodym derivative, union bound, error-transparent intertwining identity, syndrome-resolved fault model) enter the Lean development as hypotheses rather than being derived from first principles. See `lean/README.md`.

## Repository layout

- `manuscript/` — LaTeX source, compiled PDF, and Springer Nature class file.
- `notes/` — assumptions, terminology decisions, research history, and AI contribution statement.
- `scripts/` — small independent arithmetic checks for the asymptotic bounds.
- `lean/` — partial Lean 4 + mathlib formalization of the elementary arithmetic claims (`R n = n·log 2 + log 4`, the concatenation master inequality, and the KL-divergence expansion). See `lean/README.md` for scope and build instructions.
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

OpenAI ChatGPT contributed substantially to the exploratory derivation, intermediate constructions, manuscript structure, and first-draft prose. Michael A. Stay supplied the research question, introduced the branchwise nonlinear-gate idea that motivated the investigation, challenged and redirected intermediate claims, selected the scope and assumptions, and is the sole accountable author. See `notes/ai-contribution-statement.md` for the full disclosure.

## Citation

Citation metadata is provided in `CITATION.cff`. Until a stable release is made, cite the version or commit hash used.

## Contact

Dr. Michael A. Stay  
Computer Science Department, University of Auckland  
`mike@cs.auckland.ac.nz`

## License status

No reuse license has yet been selected. Unless and until a license is added, copyright remains with Michael A. Stay and no permission to reuse is implied.
