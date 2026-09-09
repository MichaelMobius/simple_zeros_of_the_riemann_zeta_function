# v20 analytic kernel proof

This directory replaces the second v17 external trust frontier by an internal analytic Lean proof.

The proved target is

```lean
(171389 / 1000000 : ℝ) < limitingk v17KernelCertPoint
```

with `v17KernelCertPoint = 89/100`.

`V20KernelSignedAnalytic.lean` derives this inequality from exact integral identities, Taylor bounds for sine and cosine, certified bounds for `π` already available in Mathlib, and rational arithmetic checked by Lean. It does not invoke the historical external interval enclosure for this point.

`V20FinalAssembly.lean` converts that theorem into `V17KernelSignedCertPointClaim` and feeds it into the existing v17 assembly. Consequently the v20 published wrapper has only one explicit external certificate input:

```lean
(hcertExt : ArchivedSevenPointClaim)
```

The numerical constant is unchanged from v17; v20 improves formal provenance rather than the quantitative bound.

CI builds both `HurtadoZeta23.V20KernelSignedAnalytic` and `HurtadoZeta23.V20FinalAssembly` on top of the pinned Anthropic `formal-math/zeta23` commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`, and rejects `sorry`/`admit` in the v20 Lean sources.

This does **not** make the formalization clean-room independent of the Anthropic software base, and it does **not** internalize the archived seven-point finite certificate. Those are separate provenance/trust-boundary facts.
