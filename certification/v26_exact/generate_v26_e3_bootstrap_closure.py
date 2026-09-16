#!/usr/bin/env python3
"""Generate the end-to-end Package E3 bootstrap closure theorem.

This file contains no new numerical mathematics.  It composes the three
kernel-checked finite reductions and the final-five closure:

    511 -> 231 -> 23 -> 5 -> False.

Its input interface is exactly the Package-D 511-word classification together
with the original word box and strict-counterexample hypothesis.
"""
from __future__ import annotations

from pathlib import Path
import argparse
import hashlib
import json


def emit() -> str:
    return '''import HurtadoZeta23.V26R0MembershipDispatchGenerated
import HurtadoZeta23.V26R1MembershipDispatchGenerated
import HurtadoZeta23.V26R2FinalClosureGenerated

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- End-to-end exact rational bootstrap closure for the 511 Package-D words.
No strict counterexample can lie in any Package-D survivor word box. -/
theorem v26_E3_close_511
    (w : V26BasinWord)
    (hmem : w ∈ v26SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  have hw1 : v26InRound1 w :=
    v26_E3_R0_reduce_511_to_231_membership
      w hmem g0 g1 g2 g3 g4 g5 hbox hbad
  have hw2 : v26InRound2 w :=
    v26_E3_R1_reduce_231_to_23_membership
      w hw1 g0 g1 g2 g3 g4 g5 hbox hbad
  exact v26_E3_close_round2
    w hw2 g0 g1 g2 g3 g4 g5 hbox hbad

/-- Equivalent non-strict lower-bound form of the full E3 finite closure. -/
theorem v26_E3_gapF_ge_delta_of_word511
    (w : V26BasinWord)
    (hmem : w ∈ v26SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5) :
    v26Delta ≤ v26GapF limitingWeight g0 g1 g2 g3 g4 g5 := by
  by_contra h
  have hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta :=
    lt_of_not_ge h
  exact v26_E3_close_511 w hmem g0 g1 g2 g3 g4 g5 hbox hbad

end HurtadoZeta23
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "V26E3BootstrapClosureGenerated.lean"
    path.write_text(emit(), encoding="utf-8")
    raw = path.read_bytes()
    manifest = {
        "chain": [511, 231, 23, 5, 0],
        "file": path.name,
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }
    (out / "v26_e3_bootstrap_closure_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print("E3 BOOTSTRAP CLOSURE GENERATION OK")
    print("chain: 511 -> 231 -> 23 -> 5 -> contradiction")


if __name__ == "__main__":
    main()
