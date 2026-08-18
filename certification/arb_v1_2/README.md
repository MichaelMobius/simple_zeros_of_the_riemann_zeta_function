# Arb/FLINT certificate v1.2

This directory records the archived proof-carrying certificate results for the nonuniform seven-point inequality.

A separate Python-standard-library checker replayed the complete finite tree and reported:

```text
certificate_structure_valid = true
prefilter_replayed = true
all_leaves_verified = true
tree_complete = true
arb_imported = false
```

See `checker_result.json`, `FINAL_AUDIT.json`, `checker_stdout.txt`, `manifest.json`, and `report.txt` for the machine-readable record, environment, counts, and SHA-256 hashes.

The complete binary payload (`kernel_table.bin`, `second_derivative_table.bin`, `tangent_bounds.bin`, `tree.bin`) is preserved in the frozen v1.2 certificate archive prepared as a `v2.0.0-formal` release asset. The hashes in `FINAL_AUDIT.json` and `manifest.json` identify those exact binaries.
