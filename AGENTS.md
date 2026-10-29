# Instructions for Codex and Other Agents

This repository contains a research draft, not an established result. Treat correctness, scope control, and traceability as higher priorities than stylistic polish.

## Read first

Before changing any substantive claim, read:

1. `README.md`
2. `manuscript/manuscript.tex`
3. `notes/assumptions-and-limitations.md`
4. `notes/ai-contribution-statement.md`

## Non-negotiable distinctions

Preserve these distinctions unless a human-author-approved derivation proves a replacement:

- `p_* = 2^{-n}` is the design weight; `p_f` is the actual marked-state weight and is either `0` or `p_*` on promised inputs.
- The initial superposition already contains every candidate basis component; the verifier marks a witness state rather than creating it.
- Use **marked state**, **marked subspace**, and **marked-state packet**, not “rare branch” or “rare flag sector.”
- Use **cumulative Born probability**, not “Born quantile.”
- A one-fault history covered by the intertwining identity, or a sequence acting only on the syndrome factor, is transparent. Do not claim that arbitrary products of individually correctable errors are transparent.
- Histories for which transparency has not been proved must be included in the nontransparent failure event.
- The full circuit has `L(n) = poly(n)` logical locations; retain the union-bound factor `L(n)`.
- The Valiant–Vazirani consequence is randomized. Keep decision, promise behavior, amplification, and SAT self-reduction separate.

## Scientific editing rules

- Do not strengthen the theorem beyond assumptions (A1)–(A4).
- Do not remove or soften the generative-AI disclosure.
- Check every algebraic change independently.
- Prefer primary sources for citations.
- Record substantive changes in `CHANGELOG.md`.
- Keep the manuscript in first-person plural (“we”), not first-person singular.
- Preserve the author’s direct explanatory voice: motivate constructions before formalizing them, and separate caveats from the main line.

## Checks before committing

```bash
make clean pdf
python3 -m unittest scripts/test_scaling.py
```

Inspect the PDF after any LaTeX change. A successful build alone does not establish correctness.
