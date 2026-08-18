# Reproducibility

## A. Arb/FLINT proof-carrying certificate v1.2

Archived artifact:

```text
certification/arb_v1_2/
```

Independent replay, without importing Arb:

```powershell
cd certification\arb_v1_2
python .\check_seven_point_certificate.py .\seven-point-cert
```

Expected terminal truth values include:

```text
certificate_structure_valid=true
prefilter_replayed=true
all_leaves_verified=true
tree_complete=true
arb_imported=false
```

Regeneration requires `python-flint>=0.9.0`.

## B. Fixed-point q60 certificate v1.3

```powershell
cd certification\fixedpoint_v1_3
python .\check_fixedpoint_certificate.py .\seven-point-fixed
```

This checker uses no Arb, python-flint, float, Fraction, Decimal, NumPy, or
external solver.

Expected result:

```text
fixedpoint_certificate_valid=true
all_leaves_verified=true
tree_complete=true
integer_only_replay=true
prefilter_identical=true
```

## C. Lean proof

The compile-confirmed working project uses Lean v4.33.0-rc2 and a pinned
Zeta23 checkout. The final release must archive the exact Lake configuration,
upstream commit, clean build output, and `#print axioms` output from the
compile-confirmed machine before tagging `v2.0.0-formal`.
