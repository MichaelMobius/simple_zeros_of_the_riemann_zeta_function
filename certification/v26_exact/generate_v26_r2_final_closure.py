#!/usr/bin/env python3
"""Generate the finite five-branch closure after the R2 membership reduction.

For each exact Round3 word, reconstruct the already certified R0, R1 and R2
contractions from the original word box.  The resulting R2 contracted box is
then identified definitionally with the corresponding Package-E final box and
closed by `v26_no_counterexample_final_<code>`.
"""
from __future__ import annotations

from pathlib import Path
import argparse
import hashlib
import json

import generate_v26_bootstrap_lean as boot

CODES = list(boot.EXPECTED_FINAL)


def branch(code: str, j: int) -> str:
    return f'''  · have hcode : v26WordCode w = {code} := hcode{j}
    have hwEq : w = v26E3R0_{code}Word := by
      apply v26_wordCode_injective
      simpa [v26E3R0_{code}Word, v26WordCode] using hcode
    rw [hwEq] at hbox
    have hR0 : v26E3R0_{code}ContractedBox g0 g1 g2 g3 g4 g5 :=
      v26_E3_R0_{code}_contract_all g0 g1 g2 g3 g4 g5 hbox hbad
    have hR1 : v26E3R1_{code}ContractedBox g0 g1 g2 g3 g4 g5 :=
      v26_E3_R1_{code}_contract_all g0 g1 g2 g3 g4 g5 hR0 hbad
    have hR2 : v26E3R2_{code}ContractedBox g0 g1 g2 g3 g4 g5 :=
      v26_E3_R2_{code}_contract_all g0 g1 g2 g3 g4 g5 hR1 hbad
    have hFinal : v26FinalBox_{code} g0 g1 g2 g3 g4 g5 := by
      simpa [v26E3R2_{code}ContractedBox, v26FinalBox_{code}] using hR2
    exact (v26_no_counterexample_final_{code}
      g0 g1 g2 g3 g4 g5 hFinal) hbad'''


def emit() -> str:
    imports = [
        "import HurtadoZeta23.V26R2MembershipDispatchGenerated",
    ]
    for code in CODES:
        imports.extend([
            f"import HurtadoZeta23.V26R0Survivor{code}Generated",
            f"import HurtadoZeta23.V26R1Survivor{code}Generated",
            f"import HurtadoZeta23.V26R2Survivor{code}Generated",
            f"import HurtadoZeta23.V26FinalBridge{code}Generated",
        ])
    rcases = " | ".join(f"hcode{i}" for i in range(len(CODES)))
    branches = "\n".join(branch(code, i) for i, code in enumerate(CODES))
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- The exact five Round3 words contain no strict counterexample once the
historical R0/R1/R2 contraction chain is reconstructed. -/
theorem v26_E3_close_final_five
    (w : V26BasinWord)
    (hw3 : v26InRound3 w)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  change v26WordCode w ∈ v26Round3Codes at hw3
  rw [v26_round3_codes_exact] at hw3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw3
  rcases hw3 with {rcases}
{branches}

/-- Closing form of the third bootstrap: Round2 membership plus a strict
counterexample is impossible. -/
theorem v26_E3_close_round2
    (w : V26BasinWord)
    (hw2 : v26InRound2 w)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  have hw3 := v26_E3_R2_reduce_23_to_5_membership
    w hw2 g0 g1 g2 g3 g4 g5 hbox hbad
  exact v26_E3_close_final_five
    w hw3 g0 g1 g2 g3 g4 g5 hbox hbad

end HurtadoZeta23
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "V26R2FinalClosureGenerated.lean"
    path.write_text(emit(), encoding="utf-8")
    raw = path.read_bytes()
    manifest = {
        "codes": CODES,
        "file": path.name,
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }
    (out / "v26_r2_final_closure_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print("R2 FINAL FIVE CLOSURE GENERATION OK")
    print("codes:", ", ".join(CODES))


if __name__ == "__main__":
    main()
