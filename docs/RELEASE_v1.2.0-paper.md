# v1.2.0-paper — v17 kernel-checked refinement

This release freezes the v17 revision of

> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**

by **Michael Hurtado**.

## Main result

The v17 manuscript establishes

\[
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
\frac{1125000H_{\rm MT}-2220}{1120671}
=0.6731175265883904388095857434\ldots,
\]

where

\[
H_{\rm MT}=\frac32-\frac1{\sqrt2}\cot\!\left(\frac1{\sqrt2}\right).
\]

The refinement uses exact pressure-preserving shifted-block accounting, adjacent-pair pinching, and block length `m = 450`.

## Lean verification

The exact Lean CI root is

```text
HurtadoZeta23.V17FinalAssembly
```

and the public final theorem is

```text
HurtadoZeta23.v17_published_eps_form_of_certificates
```

The implication from the external certificates to the published epsilon-form theorem is Lean-kernel-checked end-to-end. The exact final Hurtado import closure contains 127 modules and builds against the pinned upstream `formal-math` source tree.

The final theorem has exactly two explicit external certificate propositions:

1. `ArchivedSevenPointClaim`
2. `V17KernelSignedCertPointClaim`

The universal scalar-pressure inequality and kernel monotonicity used by v17 are proved inside Lean and are not additional external trust frontiers.

The post-merge validation on `main` completed successfully:

- `Inspect v17 final closure` — success
- `Lean v17 concrete strong block 450` — success

The build includes successful compilation of `HurtadoZeta23.V17FinalAssembly`.

## External certificate frontier 1: archived seven-point Arb/FLINT run

The historical position-dependent pressure vector is

\[
p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
\qquad \sum_jp_j=\frac1{500},
\]

and the archived 256-bit Arb/FLINT run certifies

\[
F_{6,\mathrm{nonuniform}}\ge\frac{39}{10000}.
\]

Frozen hashes:

```text
Arb verifier SHA-256:
8eb7b4a17da8e114881264d3c2fc8daf262a0558d4248692b386c0fca2cc4301

Archived 256-bit log SHA-256:
4b0e62dcb5c4014504981f16e431144e3a01184b2aa2aa6b0bf650705d59db83
```

This artifact is inherited unchanged from the earlier frozen computational release `v1.0.0-paper`.

## External certificate frontier 2: signed v17 kernel enclosure

The additional v17 numerical certificate is

\[
\frac{171389}{1000000}<k\!\left(\frac{89}{100}\right).
\]

The exact-arithmetic verifier is

```text
certification/v17/verify_improved_bound.py
```

with SHA-256

```text
73ba433447a15659a78f1485fd0403fe0fa767371ff6b22f3e6c1a1929c54208
```

and the frozen machine-readable verification file

```text
certification/v17/verification.json
```

has SHA-256

```text
c3ceab7fb966ecd9bc954da5e29414a84ef8d8a699f290a9378335a9b3542446
```

CI replays the verifier from scratch and semantically compares its output with the frozen JSON.

## Trust statement

The Lean kernel checks the complete mathematical implication from the two explicit certificate propositions above to the final v17 theorem. The external Arb/FLINT execution and the signed scalar numerical enclosure remain explicit computational trust boundaries; they are not silently introduced as Lean axioms or proof terms.

The exact final closure is audited for `sorry`, `admit`, explicit `axiom` declarations, and `unsafe` declarations.

## Main files

- `paper/main.tex`
- `paper/main.pdf`
- `certification/arb_256/`
- `certification/v17/`
- `lean_harness/`

## Previous releases

- `v1.1.0-paper` — preceding submission-ready manuscript
- `v1.0.0-paper` — frozen historical Arb/FLINT computational artifact

This file is the canonical release-note source for the `v1.2.0-paper` GitHub release.
