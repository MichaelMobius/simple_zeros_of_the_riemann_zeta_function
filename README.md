# simple_zeros_of_the_riemann_zeta_function

Reproducibility repository accompanying the manuscript
**“A position-weighted refinement for simple zeros of the Riemann zeta function.”**

## Repository layout

- `certification/arb_256/` — complete 256-bit Arb/FLINT certificate package.
- `paper/` — place the submission `.tex` and compiled PDF here.
- `docs/` — optional supplementary notes, provenance, or referee-facing documentation.

The certified computational claim is

`F6_nonuniform(g1,...,g6) >= 39/10000` for all nonnegative gaps,

with pressure vector

`(2714, 3733, 3553, 3553, 3733, 2714) / 10^7`.

The archived 256-bit run reports `verified=true`, grid denominator 4000,
1,119,372 visited nodes, and maximum branch-and-bound depth 39.

See `certification/arb_256/README.md` for exact reproduction instructions.
