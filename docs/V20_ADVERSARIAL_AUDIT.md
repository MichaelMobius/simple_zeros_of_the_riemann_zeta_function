# v20 adversarial audit — analytic signed-kernel certificate

## Scope

This audit concerns only the v20 change that replaces the historical external signed enclosure

```lean
V17KernelSignedCertPointClaim
```

by an analytic Lean theorem at the exact point `89/100`. It does not re-audit the archived seven-point certificate or claim clean-room independence from the pinned Anthropic software base.

## Claim under test

The new analytic module proves

```lean
(171389 / 1000000 : ℝ) < limitingk (89 / 100 : ℝ)
```

and `V20FinalAssembly.lean` derives `V17KernelSignedCertPointClaim` from that theorem before invoking the existing v17 final assembly.

## Adversarial checks

### 1. No circular use of the historical signed certificate

`V20KernelSignedAnalytic.lean` imports `HurtadoZeta23.LimitingKernel`, not `V17FinalAssembly`, and does not mention `V17KernelSignedCertPointClaim` or `ArchivedSevenPointClaim`. The CI workflow enforces this dependency direction by grep in the analytic source.

The imported `LimitingKernel.lean` defines

```lean
def limitingK (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
    Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t)
```

and defines `limitingk` by normalization with `limitingK 0`. Its zero-frequency formula is derived from the generic `Zeta23.ThmD.aStar_eq` identity. Thus the v20 point theorem is not obtained by importing a proposition equivalent to the target numerical enclosure.

### 2. Exact evaluation route rather than an interval oracle

At

\[
A=1/\sqrt2,\qquad B=89\pi/100,\qquad \theta=11\pi/100,
\]

Lean derives the exact formula

\[
K(0.89)=
\frac{A\sin A\cos\theta+B\cos A\sin\theta}{B^2-A^2},
\]

and the normalized identity

\[
k(0.89)=
\frac{\frac12(\sin A/A)\cos\theta+B\cos A\sin\theta}
{(B^2-\frac12)(\sin A/A)}.
\]

The derivation uses the compact cosine integral and product-to-sum identity directly in Lean.

### 3. Directed transcendental bounds

The proof establishes directed rational bounds for `π`, `sin A / A`, `cos A`, `sin θ`, `cos θ`, and `B`. Sine/cosine bounds are obtained from alternating Taylor series theorems in Mathlib. The bounds are then substituted in the direction required for a lower bound on the numerator and an upper bound on the positive denominator.

The denominator positivity is proved explicitly before cross multiplication, so the final inequality does not rely on an unchecked sign assumption.

### 4. Exact rational closure

After the transcendental quantities are replaced by directed rational bounds, the remaining strict inequality is discharged by `norm_num`. The rational safety margin is positive; numerically it is about

\[
3.04\times 10^{-6}.
\]

This is not used as floating-point evidence in the Lean proof; it merely describes the size of the exact rational margin that Lean verifies.

### 5. No new trusted declarations or placeholders

CI scans the v20 Lean sources and rejects:

- `sorry` or `admit`;
- new `axiom` or `opaque` declarations;
- `unsafe` declarations.

It separately rejects references from the analytic point-proof module back to `V17KernelSignedCertPointClaim`, `ArchivedSevenPointClaim`, `V17FinalAssembly`, or `ExternalCertificateFrontier`.

### 6. Quantitative theorem unchanged

The v20 PR adds a new analytic module, a final wrapper, documentation, and CI. It does not modify the existing v17 theorem sources or the paper. The v20 wrapper reuses `v17PublishedConstant`; therefore v20 is a provenance improvement, not a new numerical bound.

## Resulting explicit certificate frontier

The v20 published epsilon wrapper has the interface

```lean
theorem v20_published_eps_form
    (hcertExt : ArchivedSevenPointClaim) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (v17PublishedConstant - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T)
```

Hence the historical signed-kernel point enclosure is no longer an explicit external certificate input in v20. The archived seven-point finite inequality remains external.

## Residual trust and scope

The result should **not** be described as a clean-room formalization of the whole argument. The v20 modules compile as an overlay on Anthropic `formal-math/zeta23`, pinned at

```text
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
```

and reuse generic analytic definitions and lemmas from that library. The mathematical point enclosure itself, however, is derived inside Lean rather than assumed from the historical Arb certificate.

No statement in this audit substitutes for independent mathematical peer review of the full simple-zero argument.
