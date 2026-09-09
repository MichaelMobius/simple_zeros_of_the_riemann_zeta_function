# v20 adversarial audit — analytic signed-kernel certificate

## Scope

This audit concerns the v20 change that replaces the historical external signed enclosure

```lean
V17KernelSignedCertPointClaim
```

by an analytic Lean theorem at the exact point `89/100`, together with the trust-boundary hardening required after auditing the transitive axiom closure of the final wrapper. It does not re-audit the archived seven-point certificate or claim clean-room independence from the pinned Anthropic software base.

## Claim under test

The analytic module proves

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

### 5. No new trusted declarations or placeholders in v20

CI scans the v20 Lean sources and rejects:

- `sorry` or `admit`;
- new `axiom` or `opaque` declarations;
- `unsafe` declarations.

It separately rejects references from the analytic point-proof module back to `V17KernelSignedCertPointClaim`, `ArchivedSevenPointClaim`, `V17FinalAssembly`, or `ExternalCertificateFrontier`.

### 6. Transitive `native_decide` trust primitive removed from the final v20 closure

An adversarial `#print axioms HurtadoZeta23.v20_published_eps_form` audit exposed an inherited v17 primitive:

```text
HurtadoZeta23.v17_pairMultiplicitySumNat_450._native.native_decide.ax_1_1
```

The source was localized to the effective reconstructed overlay file `HurtadoZeta23/V17KernelBridge450.lean`, whose repository source is

```text
lean_harness/v17_energy/V17KernelBridge450.lean
```

The affected lemma is the finite counting identity

```lean
lemma v17_pairMultiplicitySumNat_450 :
    (∑ x ∈ Finset.range 449, (450 - (1 + x))) = 101025 := by
  calc
    (∑ x ∈ Finset.range 449, (450 - (1 + x)))
        = ∑ x ∈ Finset.range 449, ((449 - 1 - x) + 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxlt : x < 449 := Finset.mem_range.mp hx
            omega
    _ = ∑ x ∈ Finset.range 449, (x + 1) := by
          exact Finset.sum_range_reflect (fun i : ℕ => i + 1) 449
    _ = 101025 := by
          rw [Finset.sum_add_distrib, Finset.sum_range_id]
          norm_num
```

The original `native_decide` proof was first tested with ordinary `decide`; that trial did not survive the full v20 assembly build and was discarded. The final repair is symbolic: `omega` normalizes the bounded natural subtraction pointwise, `Finset.sum_range_reflect` reverses the finite sequence, and `Finset.sum_range_id` applies Gauss' summation formula. No native evaluator or brute-force `decide` remains in this lemma.

The reconstruction order matters for provenance: the workflow first extracts the historical `v17_analytic` and `v17_adj` tarballs and then copies the visible `.lean` sources into `HurtadoZeta23/`. Therefore the repaired visible `V17KernelBridge450.lean` is the source that is actually compiled by v20. This change does **not** assert that every historical `.b64` payload has been editorially normalized or that every v17 module is globally free of `native_decide`.

GitHub Actions run `34409711688`, on commit `d656cc5e5218dd09fe7b40d4f2d58c5e1f589e94`, rebuilt the reconstructed overlay against the pinned Anthropic base and passed all of the following:

- `HurtadoZeta23.V17KernelBridge450`;
- `HurtadoZeta23.V20KernelSignedAnalytic`;
- `HurtadoZeta23.V20FinalAssembly`;
- the exact transitive axiom allowlist;
- the placeholder, trusted-declaration, and dependency-direction guards.

For the three published v20 targets, the verified `#print axioms` output in that run is exactly

```text
'HurtadoZeta23.v20_kernel_signed_89_100' depends on axioms: [propext, Classical.choice, Quot.sound]
'HurtadoZeta23.v20_kernel_signed_claim' depends on axioms: [propext, Classical.choice, Quot.sound]
'HurtadoZeta23.v20_published_eps_form' depends on axioms: [propext, Classical.choice, Quot.sound]
```

CI treats these closures as allowlisted interfaces. It additionally audits `v17_pairMultiplicitySumNat_450` directly and requires its axiom closure to be empty. Any additional axiom, including `sorryAx` or a `_native.native_decide.ax_...` primitive, makes the workflow fail. This is stronger than merely grepping the source for new declarations.

### 7. Quantitative theorem unchanged

The trust-boundary repair changes one proof implementation in the v17 support source and hardens CI; it does not change the theorem statement, the signed-kernel inequality, `v17PublishedConstant`, or the paper's numerical result. The bound remains

\[
0.6731175265883904388095857434106058666\ldots.
\]

Thus v20 remains a provenance/formalization improvement rather than a new numerical bound.

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

Hence the historical signed-kernel point enclosure is no longer an explicit external certificate input in v20. The archived seven-point finite inequality remains external. A theorem parameter such as `hcertExt : ArchivedSevenPointClaim` is a mathematical hypothesis in the theorem interface; it is not a Lean kernel axiom and therefore does not appear in `#print axioms`.

## Residual trust, provenance, and scope

The result should **not** be described as a clean-room formalization of the whole argument. The v20 modules compile as an overlay on Anthropic `formal-math/zeta23`, pinned at

```text
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
```

and reuse generic analytic definitions and lemmas from that library. This is a statement about software provenance. It is distinct from the mathematical-independence claim: the new point enclosure is derived inside Lean rather than assumed from the historical Arb certificate, and the final mathematical result does not use Anthropic's principal numerical conclusion as a black box.

The historical release `v1.2.0-paper` is outside the scope of this hardening and is not modified.

No statement in this audit substitutes for independent mathematical peer review of the full simple-zero argument.
