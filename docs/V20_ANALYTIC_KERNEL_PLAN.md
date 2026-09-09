# v20 analytic kernel certificate

Goal: replace the external proposition

```lean
V17KernelSignedCertPointClaim : Prop :=
  (171389 / 1000000 : ℝ) < limitingk v17KernelCertPoint
```

by a theorem checked inside Lean.

The target is unchanged:

```text
k(89/100) > 171389/1000000.
```

The intended analytic route is:

1. derive a closed form for the limiting Montgomery--Taylor kernel from the compact cosine integral;
2. reduce the point `x = 89/100` to positive-angle expressions at `11π/100`;
3. prove rational lower/upper bounds for π by the Machin identity and alternating arctangent series;
4. prove rational Taylor bounds for `sin(11π/100)` and `cos(11π/100)`;
5. prove a rational lower bound for `sqrt(2) * cot(1/sqrt(2))` using alternating sine/cosine series;
6. close the final strict inequality with exact rational arithmetic (`norm_num`/`ring_nf`).

No numerical interval oracle is permitted in the final theorem.  The branch remains experimental until the module compiles without `sorry`/`admit` and the final v17 assembly is rewired to consume the theorem directly.
