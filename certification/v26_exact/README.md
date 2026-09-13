# v26 exact rational bootstrap

This directory contains the reproducible exact-rational layer for the v26 six-gap bootstrap.

The computation uses Python integer arithmetic and `fractions.Fraction` only. It uses no floating point, Arb/FLINT, interval arithmetic, grid search, branch-and-bound, SDP, or numerical solver.

`v21_rational_bootstrap_verify.py` regenerates the historical certificate

`44100 -> 511 -> 231 -> 23 -> 5`

and writes `/mnt/data/v21_rational_bootstrap_certificate.json`. CI requires the regenerated file to have SHA256

`5234366c615d599a7afd3f85bf82cb04272a158171e5e5fb144fcf23941b0eb4`.

`generate_v26_bootstrap_lean.py` independently regenerates the rational quadratic forms for all bootstrap discards. Each positive-definite 6x6 quadratic is decomposed exactly as `L D L^T`, producing a six-square certificate. The generated Lean modules are temporary build products and are not committed to the repository.

For every discarded word, Lean checks:

1. the exact completion-of-squares identity with `ring`;
2. nonnegativity of the six-square remainder with `positivity`;
3. the strict rational margin above `39/10000` with `norm_num`.

Therefore the Python generator is not a proof oracle: incorrect generated coefficients cause kernel verification to fail. The analytic statement that each rounded quadratic is a lower bound for the original kernel functional is handled separately by the v26 analytic-minorant layer.

The GitHub Actions workflow `.github/workflows/v26-package-b.yml` performs the regeneration and Lean kernel check from a pinned `formal-math/zeta23` base.
