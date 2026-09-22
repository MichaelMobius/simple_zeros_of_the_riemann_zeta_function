# Manuscript

This directory contains the current submission-ready manuscript for

**Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**

by Michael Hurtado.

- `main.tex` — complete LaTeX source.
- `main.pdf` — PDF regenerated automatically from `main.tex` by GitHub Actions.

The manuscript proves the dyadic lower bound
[
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
\frac{1125000H_{\rm MT}-2220}{1120671}
=
0.6731175265883904\ldots .
]

The finite six-gap certificate is reproduced from exact rational data in
`../certification/v26_exact/`.  Its checked reduction is

`44100 -> 511 -> 231 -> 23 -> 5 -> contradiction`.

The formal theorem state cited by the manuscript is project commit
`e0f67e112f59b31a4278e1d56377f5e4f1628836`, built on the pinned
Anthropic `formal-math/zeta23` source tree at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.

The literal liminf theorem is kernel-checked in CI.  Its transitive axiom
closure is required to be exactly

`propext, Classical.choice, Quot.sound`

and the workflow also rejects `sorryAx`.

For the independent Arb/FLINT interval-arithmetic reproduction of the
seven-point inequality, see:

`../certification/arb_256/README.md`

For the exact rational certificate generators and their trust model, see:

`../certification/v26_exact/README.md`
