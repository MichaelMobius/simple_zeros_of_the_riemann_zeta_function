# v20 analytic kernel certificate

## Status

The planned replacement of the v17 signed-kernel external enclosure is complete on the v20 branch.

Lean proves

```lean
(171389 / 1000000 : ℝ) < limitingk (89 / 100 : ℝ)
```

inside `V20KernelSignedAnalytic.lean`, and `V20FinalAssembly.lean` feeds this theorem into the existing v17 assembly.

## Analytic route actually formalized

The final proof differs from the initial plan in two useful ways: it avoids a separate Machin-identity development for π, and it avoids formalizing a universal cotangent closed form for the kernel.

At the single required point, set

\[
A=1/\sqrt2,\qquad B=89\pi/100,\qquad \theta=11\pi/100.
\]

The compact cosine integral and product-to-sum identity give the exact point formula

\[
K(0.89)=
\frac{A\sin A\cos\theta+B\cos A\sin\theta}{B^2-A^2}.
\]

After normalizing by `K(0)`, Lean rewrites this as

\[
k(0.89)=
\frac{\frac12\frac{\sin A}{A}\cos\theta+B\cos A\sin\theta}
{(B^2-\frac12)\frac{\sin A}{A}}.
\]

The proof then uses:

1. alternating Taylor bounds for sine and cosine proved from Mathlib's series theorems;
2. proved Mathlib rational bounds for π;
3. exact identities for powers of `A = 1/sqrt 2`;
4. directed rational lower/upper bounds for `sin A / A`, `cos A`, `sin θ`, `cos θ`, and `B`;
5. a final all-rational strict margin discharged by `norm_num`.

No external interval oracle is used for the signed kernel point in v20.

## Resulting trust boundary

The v20 published wrapper has one explicit external certificate input:

```lean
(hcertExt : ArchivedSevenPointClaim)
```

The historical v17 signed-kernel proposition is derived internally in v20. The archived seven-point finite certificate remains external.

The Lean modules still compile as an overlay on the pinned Anthropic `formal-math/zeta23` software base at commit

```text
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
```

so this provenance improvement must not be described as a clean-room formalization independent of that library.

The numerical simple-zero constant is unchanged from v17; v20 strengthens formal provenance rather than the quantitative bound.
