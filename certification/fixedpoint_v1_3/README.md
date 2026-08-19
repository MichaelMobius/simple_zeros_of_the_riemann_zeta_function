# Fixed-point q60 certificate v1.3

This directory records the exact integer-only replay results used to bridge the archived finite certificate to the Lean formalization.

The checker reported:

```text
fixedpoint_certificate_valid = true
integer_only_replay = true
prefilter_identical = true
all_leaves_verified = true
tree_complete = true
hessian_check = exact integer Bareiss / Sylvester
scale_bits = 60
```

Minimum post-quantization margins:

```text
minimum_interval_margin_real = 5.598149478924466e-10
minimum_tangent_margin_real  = 2.9986027445962243e-9
```

See `FIXEDPOINT_AUDIT.json` and `manifest-fixed.json` for the complete machine-readable result, exact counts, encoding description, and SHA-256 hashes.

The large q60 binary payloads are preserved in the frozen v1.3 certificate archive prepared as a `v2.0.0-formal` release asset. Their exact SHA-256 hashes are recorded in `manifest-fixed.json`.
