# Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function

This repository contains the manuscript, formal verification, and reproducibility artifacts for

> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**

by **Michael Hurtado**.

## Main result

The manuscript proves the unconditional dyadic lower bound

$$
\boxed{
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
\frac{1125000H_{\rm MT}-2220}{1120671}
}
$$

where

$$
H_{\rm MT}
=
\frac32-\frac1{\sqrt2}\cot\!\left(\frac1{\sqrt2}\right),
$$

so numerically

$$
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
0.6731175265883904388095857434\ldots .
$$

This is a result about the proportion of **simple zeros on the critical line**. It is not a proof of the Riemann Hypothesis and does not assert that all nontrivial zeros are simple.

## Manuscript

The current publication files are:

- [`paper/main.tex`](paper/main.tex) — complete LaTeX source.
- [`paper/main.pdf`](paper/main.pdf) — compiled manuscript.
- [`paper/REPRODUCIBILITY.md`](paper/REPRODUCIBILITY.md) — exact manuscript/formal snapshot.

The paper is written as a self-contained mathematical article relative to the classical analytic and matrix results it cites. Internal development-version names are repository implementation details and are not part of the manuscript narrative.

## Proof architecture

The argument combines:

1. a stability-enhanced rank--trace inequality;
2. exact pressure-preserving shifted-block averaging;
3. adjacent-pair pinching for the Gram defect;
4. an analytic signed-kernel estimate;
5. a certified position-weighted seven-point inequality;
6. an exact rational finite closure of the remaining six-gap hard core.

The pressure vector is

$$
p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
\qquad
\sum_{j=1}^6p_j=\frac1{500}.
$$

The finite certificate closes the exact chain

```text
44100 -> 511 -> 231 -> 23 -> 5 -> contradiction
```

with round accounting

```text
511 = 280 + 231
231 = 208 + 23
 23 =  18 +  5
```

and terminal words

```text
121212
121221
122121
212121
212212
```

Each of the five final rational quadratic minima lies strictly above
`39/10000`; the smallest exact margin is greater than `1/2000000`.

## Formal verification

The companion Lean development proves the article's seven-point inequality, the published epsilon-form estimate, and the literal endpoint

$$
\frac{1125000H_{\rm MT}-2220}{1120671}
\le
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}.
$$

The formal environment is pinned to:

```text
Anthropic formal-math: fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
Lean:                  v4.33.0-rc2
mathlib:               51e6992efd06126df61a496bebf8f49482a4e129
```

The publication CI regenerates the exact finite certificate stack and checks the final theorem with the exact transitive axiom whitelist

```text
propext
Classical.choice
Quot.sound
```

and rejects `sorryAx`.

A cold rebuild of the final theorem dependency graph has also completed successfully. This is a standard Lean/Mathlib trust boundary; the development is not described as axiom-free.

## Reproducibility

### Exact rational certificate

[`certification/v26_exact/`](certification/v26_exact/) contains the exact-rational certificate generators and documentation. Python is used to produce certificate data, but the generated Lean modules recheck the mathematical obligations: interval membership, analytic minorants, rational quadratic identities, positivity, discard margins, contractions, membership routing, and the five final closures.

### Independent Arb/FLINT check

[`certification/arb_256/`](certification/arb_256/) contains an independent interval-arithmetic reproduction of the seven-point inequality. It is retained as a separate reproducibility check and is not a premise of the final Lean theorem path.

## Repository structure

```text
.
├── paper/
│   ├── main.tex
│   ├── main.pdf
│   └── REPRODUCIBILITY.md
├── certification/
│   ├── v26_exact/
│   └── arb_256/
├── lean_harness/
│   └── ...
├── .github/workflows/
├── CITATION.cff
├── LICENSE-CODE
└── LICENSE-CONTENT
```

The internal directory and theorem names preserve development compatibility; the manuscript itself presents only the final mathematical argument.

## Licenses

Source code, certificate generators, and reproduction scripts are released under the **MIT License** unless otherwise stated; see `LICENSE-CODE`.

The manuscript, documentation, certificate metadata, and other non-software material are released under **CC BY 4.0**; see `LICENSE-CONTENT`.

Third-party dependencies retain their respective licenses.

## Citation

Please cite the accompanying manuscript when using the mathematical result. If you use or reproduce the formal or computational artifacts, also cite this repository. Citation metadata is provided in [`CITATION.cff`](CITATION.cff).

## Author

**Michael Hurtado**

Repository: https://github.com/MichaelMobius/simple_zeros_of_the_riemann_zeta_function
