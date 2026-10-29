# Manuscript

`manuscript.tex` is the editable source and `manuscript.pdf` is the current compiled draft.

The source uses Springer Nature’s generic `sn-jnl` class with the numbered math/physics reference option. The repository is no longer tied to a journal submission, but the class is retained because the current manuscript was developed in that format.

Build from the repository root with:

```bash
make pdf
```

The bibliography is embedded in `manuscript.tex`; no separate BibTeX database is required.
