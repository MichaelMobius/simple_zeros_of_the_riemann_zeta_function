# v20 analytic kernel proof

This directory is an experimental replacement for the second v17 external trust frontier.

The proof target is

```lean
(171389 / 1000000 : ℝ) < limitingk v17KernelCertPoint
```

with `v17KernelCertPoint = 89/100`.

The final accepted version must contain no `sorry`, `admit`, external interval certificate, or imported theorem whose statement merely restates the target numerical enclosure.
