# Historical v17 revision machinery

> **Historical archive — not the current manuscript or current priority statement.**
>
> The publication manuscript is `paper/main.tex`.  The current exact finite
> certificate and formal endpoint are documented in `paper/REPRODUCIBILITY.md`
> and `certification/v26_exact/`.  Files in this directory preserve the
> earlier v17 source-transformation/provenance record and must not be read as
> statements about the present proof state.

This directory contains the fail-closed source transformation that was used to
build the pressure-preserving v17 manuscript from the audited v16
`paper/main.tex`.

`apply.py` checks the exact Git blob SHA of the v16 source before applying any
replacement.  The historical generated manuscript was validated by GitHub
Actions using exact-arithmetic verification, semantic comparison with the
then-frozen certificate, LaTeX compilation, and reference/label checks.

The statements in `priority.tex`, `trust.tex`, and the other fragments
describe that historical revision only.  In particular, their references to an
inherited frozen seven-point certificate predate the current exact-rational
finite closure

`44100 -> 511 -> 231 -> 23 -> 5 -> contradiction`

and the current literal Lean liminf endpoint.
