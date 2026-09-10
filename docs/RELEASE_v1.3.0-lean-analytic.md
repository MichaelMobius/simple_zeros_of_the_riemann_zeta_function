# v1.3.0-lean-analytic — analytic Lean kernel certificate

This release freezes the v20 formal-provenance hardening of

> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**

by **Michael Hurtado**.

The mathematical theorem, numerical bound, and underlying v17 argument are unchanged from `v1.2.0-paper`; the manuscript itself subsequently received v18/v19 provenance and publication-hardening revisions, and the present v20 revision aligns its formal-verification discussion with the analytic Lean certificate. One numerical certificate that was an explicit external input in v17 is now proved analytically inside Lean, and the resulting trust boundary is audited explicitly.

## Main result

The published lower bound remains

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

No numerical constant is changed by v20.

## What changes in v20

In v17, the final Lean wrapper exposed two explicit external certificate propositions:

1. `ArchivedSevenPointClaim`
2. `V17KernelSignedCertPointClaim`

The second proposition is the signed limiting-kernel inequality

\[
\frac{171389}{1000000}<k\!\left(\frac{89}{100}\right).
\]

In v20 this inequality is proved in Lean itself. The exact theorem is

```text
HurtadoZeta23.v20_kernel_signed_89_100
```

inside

```text
HurtadoZeta23.V20KernelSignedAnalytic
```

and the final wrapper is assembled in

```text
HurtadoZeta23.V20FinalAssembly
```

with public epsilon-form theorem

```text
HurtadoZeta23.v20_published_eps_form
```

The v20 wrapper therefore has exactly one explicit external mathematical certificate argument:

```text
ArchivedSevenPointClaim
```

The historical seven-point Arb/FLINT certificate remains unchanged and remains the explicit external mathematical trust frontier.

## Analytic Lean proof of the signed kernel point

`V20KernelSignedAnalytic.lean` proves

```text
(171389 / 1000000 : ℝ) < limitingk (89 / 100 : ℝ)
```

using exact integral identities, rigorous rational Taylor bounds for sine and cosine, proved Mathlib bounds for `π`, and exact rational arithmetic. The proof does not consume the v17 Python certificate as a theorem input.

The historical verifier

```text
certification/v17/verify_improved_bound.py
```

and its frozen machine-readable output remain in the repository as reproducibility and provenance artifacts. They are no longer an explicit mathematical input to the v20 published wrapper.

## Native-evaluator trust hardening

A transitive adversarial audit of the v20 theorem closure found that the inherited v17 finite pair-count lemma

```text
HurtadoZeta23.v17_pairMultiplicitySumNat_450
```

had previously been discharged using `native_decide`. That introduced a native-evaluator primitive into the final theorem's axiom report.

The lemma is now proved symbolically using finite-sum identities, `Finset.sum_range_reflect`, `Finset.sum_range_id`, and arithmetic normalization. The repaired proof contains neither `native_decide` nor a direct brute-force `decide` replacement.

This is a formal trust hardening, not a change to the mathematical statement.

## Axiom-closure audit

CI prints and checks the axiom closures of

```text
HurtadoZeta23.v17_pairMultiplicitySumNat_450
HurtadoZeta23.v20_kernel_signed_89_100
HurtadoZeta23.v20_kernel_signed_claim
HurtadoZeta23.v20_published_eps_form
```

and requires the exact standard Mathlib closure

```text
[propext, Classical.choice, Quot.sound]
```

for all four targets.

CI rejects both

```text
sorryAx
_native.native_decide.ax_
```

from those audited closures. It also rejects `sorry`/`admit` in the v20 sources, new `axiom`/`opaque`/`unsafe` declarations there, and circular dependencies from the analytic proof back to the historical signed-certificate frontier.

Accordingly, “kernel-checked” here means that Lean checks the proof terms under the explicit standard Mathlib axiom boundary above. It does not mean that the development is constructively axiom-free.

## Final audited CI

The final pre-merge closure run for the audited v20 branch was

```text
GitHub Actions run: 34428159178
Audited branch HEAD: ebf11ae228638e32d4e77a99e78f405ee1600dea
```

and completed successfully for:

- reconstruction of the pinned source overlay;
- the symbolic pair-count guard;
- `HurtadoZeta23.V17KernelBridge450`;
- `HurtadoZeta23.V20KernelSignedAnalytic`;
- `HurtadoZeta23.V20FinalAssembly`;
- exact axiom allowlisting;
- placeholder rejection;
- trusted/unsafe-declaration rejection;
- analytic dependency-direction checks.

The audited v20 implementation was merged into `main` by PR #11 as

```text
fe2eef5516c9eb3443c0d2a7f22b73a5f2afb986
```

before this release-preparation commit.

## Software provenance

This release is not a clean-room formalization independent of upstream software. The v20 CI reconstructs the repository overlay on top of the pinned Anthropic `formal-math/zeta23` commit

```text
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
```

The distinction is therefore:

- **mathematical external certificate frontier:** only `ArchivedSevenPointClaim` in the v20 wrapper;
- **software provenance:** the pinned upstream `formal-math/zeta23` source base remains part of the implementation provenance.

## Historical seven-point certificate

The archived position-dependent pressure vector remains

\[
p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
\qquad \sum_jp_j=\frac1{500},
\]

and the frozen 256-bit Arb/FLINT run certifies

\[
F_{6,\mathrm{nonuniform}}\ge\frac{39}{10000}.
\]

Frozen hashes remain unchanged:

```text
Arb verifier SHA-256:
8eb7b4a17da8e114881264d3c2fc8daf262a0558d4248692b386c0fca2cc4301

Archived 256-bit log SHA-256:
4b0e62dcb5c4014504981f16e431144e3a01184b2aa2aa6b0bf650705d59db83
```

This artifact is inherited unchanged from `v1.0.0-paper`.

## Unchanged artifacts

The following are intentionally unchanged by this release:

- the numerical lower bound;
- the v17 manuscript in `paper/main.tex` and `paper/main.pdf`;
- the historical seven-point Arb/FLINT certificate;
- the frozen `v1.2.0-paper` release;
- the v17 exact-arithmetic verifier and verification JSON, retained as historical reproducibility artifacts.

## Main v20 files

- `lean_harness/v20_analytic/V20KernelSignedAnalytic.lean`
- `lean_harness/v20_analytic/V20FinalAssembly.lean`
- `lean_harness/v17_energy/V17KernelBridge450.lean`
- `.github/workflows/v20-analytic-kernel.yml`
- `docs/V20_ADVERSARIAL_AUDIT.md`
- `docs/V20_ANALYTIC_KERNEL_PLAN.md`

## Previous releases

- `v1.2.0-paper` — v17 kernel-checked refinement with two explicit certificate frontiers
- `v1.1.0-paper` — preceding submission-ready manuscript
- `v1.0.0-paper` — frozen historical Arb/FLINT computational artifact

This file is the canonical release-note source for the `v1.3.0-lean-analytic` GitHub release.
