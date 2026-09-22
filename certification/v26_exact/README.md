# Exact rational six-gap certificate

This directory contains the reproducible exact-rational certificate used by
the manuscript's six-gap closure.

The certificate arithmetic uses Python integers and `fractions.Fraction`
only.  It does not use floating point, Arb/FLINT, interval arithmetic,
grid search, branch-and-bound, SDP, or a numerical optimizer.

The finite reduction is

`44100 -> 511 -> 231 -> 23 -> 5 -> contradiction`.

The first step is the exact one-body basin enumeration.  The three subsequent
bootstrap rounds use rational one-variable kernel minorants, six-variable
quadratic lower bounds, exact LDL^T completion, and rational contraction.
The five terminal boxes are closed by strong-convexity lower quadratics whose
exact minima lie strictly above `39/10000`.

`v21_rational_bootstrap_verify.py` independently regenerates the finite
bookkeeping and exact rational data.  The `generate_v26_*.py` scripts then
emit Lean modules for the analytic minorants, discard certificates,
contractions, membership routing, final five minima, and the composed
end-to-end closure.

The Python scripts are certificate producers, not trusted proof oracles.
The generated Lean modules recheck the mathematical obligations, including:

1. interval membership and one-variable minorant hypotheses;
2. algebraic identities for the assembled rational quadratics;
3. positivity of exact LDL^T / sum-of-squares coefficients;
4. strict rational discard margins;
5. weighted-Cauchy contraction implications;
6. exact routing of every input code to either a discard or the next survivor
   set;
7. the five final strong-convexity lower bounds.

Incorrect generated data therefore causes Lean elaboration or kernel checking
to fail rather than becoming an additional assumption.

The complete publication endpoint is rebuilt by
`.github/workflows/v26-published-liminf.yml`.  That workflow reconstructs
the pinned `formal-math/zeta23` base, regenerates the complete exact
certificate stack, kernel-checks the literal liminf theorem, rejects
`sorryAx`, and requires its transitive axiom closure to be exactly

`propext, Classical.choice, Quot.sound`.

The pinned formal base is Anthropic `formal-math` commit

`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`

with Lean `v4.33.0-rc2` and mathlib commit

`51e6992efd06126df61a496bebf8f49482a4e129`.
