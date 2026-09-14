#!/usr/bin/env python3
"""Apply module-level Lean resource limits to the generated R0 dispatch base.

The exact 511 = 280 + 231 partition and cardinality statements are large
finite expressions.  Their theorem *statements* may require more elaboration
resources before a proof-local `set_option` takes effect.  This normalizer
therefore installs the same trusted-kernel settings at module scope.  It does
not alter any proposition or proof term and does not introduce proof
shortcuts.
"""
from pathlib import Path
import argparse


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    path = Path(ns.out_dir) / "V26R0DispatchBaseGenerated.lean"
    text = path.read_text(encoding="utf-8")
    needle = "noncomputable section\nnamespace HurtadoZeta23\n"
    replacement = (
        "set_option maxHeartbeats 0\n"
        "set_option maxRecDepth 100000\n\n"
        + needle
    )
    if needle not in text:
        raise RuntimeError("dispatch base insertion point not found")
    if "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n" in text:
        print("R0 DISPATCH NORMALIZATION ALREADY PRESENT")
        return
    path.write_text(text.replace(needle, replacement, 1), encoding="utf-8")
    print("R0 DISPATCH MODULE-LEVEL LIMITS INSTALLED")


if __name__ == "__main__":
    main()
