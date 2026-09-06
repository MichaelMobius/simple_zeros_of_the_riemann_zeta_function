# v17 revision machinery

This directory contains the fail-closed source transformation used to build the
pressure-preserving v17 manuscript from the audited v16 `paper/main.tex`.

`apply.py` checks the exact Git blob SHA of the v16 source before applying any
replacement.  The generated `paper/main_v17.tex` is validated by GitHub Actions:

1. exact-arithmetic verification;
2. semantic equality with the frozen `verification.json`;
3. LaTeX compilation;
4. undefined-reference and duplicate-label checks.

Only after all checks pass does CI promote the generated source and PDF on the
review branch.  The seven-point Arb/FLINT certificate itself is inherited
unchanged from the frozen v1.0.0-paper artifact.
