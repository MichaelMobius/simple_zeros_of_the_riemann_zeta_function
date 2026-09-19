#!/usr/bin/env python3
"""Insert the definitional bridge between the R1 pilot Q and bootstrap Q.

Both definitions are emitted from the same exact Fraction data, but Lean's
`rw` does not rewrite across two different constant names automatically.  We
make that equality explicit and then use it before the analytic Q=assembly
identity.  No proposition or numeric certificate is changed.
"""
from pathlib import Path
import argparse
import re


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    path = Path(ns.out_dir) / "V26R1DiscardPilotGenerated.lean"
    text = path.read_text(encoding="utf-8")
    m = re.search(r"v26Q_R1_(\d{6})", text)
    if not m:
        raise RuntimeError("could not identify R1 bootstrap word code")
    code = m.group(1)

    if "v26_E3_R1_pilot_bootstrap_Q_eq" not in text:
        needle = "/-- Symbolic-root analytic assembly on the exact R0-contracted input box. -/\n"
        bridge = f'''/-- The pilot Q is definitionally the exact historical bootstrap R1 Q. -/
theorem v26_E3_R1_pilot_bootstrap_Q_eq
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Q_R1_{code} x0 x1 x2 x3 x4 x5 =
      v26E3R1PilotQ x0 x1 x2 x3 x4 x5 := by
  unfold v26Q_R1_{code} v26E3R1PilotQ
  rfl

'''
        if needle not in text:
            raise RuntimeError("pilot assembly insertion point not found")
        text = text.replace(needle, bridge + needle, 1)

    old = "  rw [v26_E3_R1_pilot_Q_eq_assembled]\n"
    new = "  rw [v26_E3_R1_pilot_bootstrap_Q_eq, v26_E3_R1_pilot_Q_eq_assembled]\n"
    if old in text:
        text = text.replace(old, new, 1)
    elif new not in text:
        raise RuntimeError("pilot Q_le rewrite site not found")

    path.write_text(text, encoding="utf-8")
    print("R1 DISCARD PILOT Q BRIDGE INSTALLED")
    print("word:", code)


if __name__ == "__main__":
    main()
