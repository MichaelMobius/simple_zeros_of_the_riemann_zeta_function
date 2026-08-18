# Certification results

This directory records the audited results of the two finite-certificate layers used for the seven-point inequality

```math
\mathcal F_p(g)\ge \frac{39}{10000},
```

with pressure vector

```math
p=\frac{1}{10^7}(2714,3733,3553,3553,3733,2714).
```

## Arb/FLINT certificate v1.2

The archived standard-library-only checker completed successfully with:

- `certificate_structure_valid = true`
- `prefilter_replayed = true`
- `all_leaves_verified = true`
- `tree_complete = true`
- `arb_imported = false`
- nodes: `1,119,372`
- splits: `559,038`
- pressure leaves: `5,269`
- interval leaves: `364,112`
- tangent leaves: `190,953`
- maximum depth: `39`
- archived elapsed time: `177.894336651 s`

Archived environment:

- Python `3.12.13`
- `python-flint 0.9.0`
- Linux x86_64
- Tesla T4, 15360 MiB

Principal v1.2 SHA-256 hashes:

| file | SHA-256 |
|---|---|
| `kernel_table.bin` | `f75a3968f6daf7ea74867e430dc69fdca4276c4bb09f8cecc1b9846e8942c3f5` |
| `second_derivative_table.bin` | `f878d03d2eeca7fd34e3064a8dacb70d054fe3b3e9e3890c79a1f8297633cfb3` |
| `tangent_bounds.bin` | `b0dd7dc78334ba9de6961e150c5e39a0b07c40077f253a06d01f7188a9a37628` |
| `tree.bin` | `3ea583db3cd2fde0cb46cc409a0c0df5c01c384cdfccd8720133cfee1aa5d2aa` |
| manifest | `c8c45f4ce71f6fedddedb9b6475fe2fa7d494cb6f4f658738e3499eed541a639` |

The detailed archived result is in `arb_v1_2/checker_result.json` and `arb_v1_2/FINAL_AUDIT.json`.

## Fixed-point q60 certificate v1.3

The exact integer-only replay completed successfully with:

- `fixedpoint_certificate_valid = true`
- `integer_only_replay = true`
- `prefilter_identical = true`
- `all_leaves_verified = true`
- `tree_complete = true`
- Hessian check: exact integer Bareiss / Sylvester
- scale bits: `60`
- nodes: `1,119,372`
- splits: `559,038`
- pressure leaves: `5,269`
- interval leaves: `364,112`
- tangent leaves: `190,953`
- maximum depth: `39`
- minimum interval margin: `5.598149478924466e-10`
- minimum tangent margin: `2.9986027445962243e-9`

Principal v1.3 SHA-256 hashes:

| file | SHA-256 |
|---|---|
| `kernel_q60.i64` | `a16cce93ee3ffeab9c1242f9cee1636d7de5843f20c2c4c894cc04ae1f37740a` |
| `second_q60.i64` | `5a460c9f44b16d13d9ebee5ebe8f37c0caac6f4f5befb15476a49255d08376f6` |
| `tangent_q60.i64` | `6d7c646217dc27a6ebfed3c9eaeb00dee3446032ed6825abff215888ebbb60df` |
| `tree_4bit.bin` | `edc7778018342d35d81b1d98d22e2f4c873dd6bce7bf86f1b4d20837cdf7984a` |

The detailed result and exact certificate metadata are in `fixedpoint_v1_3/FIXEDPOINT_AUDIT.json` and `fixedpoint_v1_3/manifest-fixed.json`.

## Binary certificate payloads

The large binary certificate tables are preserved in the frozen certificate archives prepared for `v2.0.0-formal`. Their hashes above identify the exact payloads. The GitHub release assets are intended to contain the complete v1.2 and v1.3 ZIP archives; this repository directory keeps the human-readable audit trail and machine-readable result metadata.
