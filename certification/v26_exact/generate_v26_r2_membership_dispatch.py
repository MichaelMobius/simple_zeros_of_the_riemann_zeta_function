#!/usr/bin/env python3
"""Generate the kernel-checkable membership-only R2 router.

Starting from membership in the exact 23-word Round2 table and the original
word box, each of the 18 R2-discard branches reconstructs its concrete R0 and
R1 contraction certificates and feeds the resulting R1-contracted box to the
R2 analytic discard theorem.

The aggregate theorem is the exact finite reduction needed by the endgame:
strict counterexample + Round2 membership => Round3 membership (five words).
"""
from __future__ import annotations

from pathlib import Path
import argparse
import hashlib
import json

import generate_v26_bootstrap_lean as boot

v = boot.v
CHUNK = 10


def wcode(w) -> str:
    return "".join(map(str, w))


def code_finset(codes: list[str]) -> str:
    assert codes
    return "{" + ", ".join(codes) + "}"


def union_expr(names: list[str]) -> str:
    assert names
    out = names[-1]
    for name in reversed(names[:-1]):
        out = f"{name} ∪ ({out})"
    return out


def exact_data():
    words511, _ = v.enumerate_511()
    r0, d0 = v.run_round(words511, initial=True)
    r1, d1 = v.run_round(r0)
    r2, d2 = v.run_round(r1)
    assert len(r0) == 231 and len(d0) == 280
    assert len(r1) == 23 and len(d1) == 208
    assert len(r2) == 5 and len(d2) == 18
    assert tuple(wcode(x[0]) for x in r2) == boot.EXPECTED_FINAL
    scodes = {wcode(x[0]) for x in r2}
    dcodes = {wcode(x[0]) for x in d2}
    assert scodes.isdisjoint(dcodes)
    assert scodes | dcodes == {wcode(x[0]) for x in r1}
    return r1, r2, d2


def emit_base(discards):
    dcodes = [wcode(x[0]) for x in discards]
    chunks = [dcodes[i:i + CHUNK] for i in range(0, len(dcodes), CHUNK)]
    names = [f"v26E3R2MembershipDiscardChunk{i:02d}" for i in range(len(chunks))]
    defs = [
        f"def {name} : Finset Nat := {code_finset(codes)}"
        for name, codes in zip(names, chunks)
    ]
    return f'''import HurtadoZeta23.V26BasinInterface
import HurtadoZeta23.V26BootstrapStageLists
import HurtadoZeta23.V26WordCodeInjective
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

{chr(10).join(defs)}

/-- Exact union of the 18 R2 discard codes. -/
def v26E3R2MembershipDiscardCodes : Finset Nat :=
  {union_expr(names)}

/-- The 18 explicit R2 discard codes are exactly Round2 minus Round3. -/
theorem v26_E3_R2_membership_discardCodes_exact :
    v26E3R2MembershipDiscardCodes = v26Round2Codes \\ v26Round3Codes := by
  decide

end HurtadoZeta23
''', names, chunks


def emit_chunk(idx: int, codes: list[str], name: str) -> str:
    imports = [
        "import HurtadoZeta23.V26R2MembershipDispatchBaseGenerated",
        f"import HurtadoZeta23.V26R2AnalyticDiscards{idx:02d}Generated",
    ]
    for code in codes:
        imports.append(f"import HurtadoZeta23.V26R0Survivor{code}Generated")
        imports.append(f"import HurtadoZeta23.V26R1Survivor{code}Generated")

    branches = []
    for j, code in enumerate(codes):
        branches.append(f'''  · have hcode : v26WordCode w = {code} := hcode{j}
    have hwEq : w = v26E3R0_{code}Word := by
      apply v26_wordCode_injective
      simpa [v26E3R0_{code}Word, v26WordCode] using hcode
    rw [hwEq] at hbox
    have hR0 : v26E3R0_{code}ContractedBox g0 g1 g2 g3 g4 g5 :=
      v26_E3_R0_{code}_contract_all g0 g1 g2 g3 g4 g5 hbox hbad
    have hR1 : v26E3R1_{code}ContractedBox g0 g1 g2 g3 g4 g5 :=
      v26_E3_R1_{code}_contract_all g0 g1 g2 g3 g4 g5 hR0 hbad
    exact (v26_E3_R2_no_counterexample_{code}
      g0 g1 g2 g3 g4 g5 hR1) hbad''')
    rcases = " | ".join(f"hcode{i}" for i in range(len(codes)))
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- A strict counterexample cannot have an R2 discard code in chunk {idx}. -/
theorem v26_E3_R2_membership_no_bad_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ {name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [{name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(branches)}

end HurtadoZeta23
'''


def emit_aggregate(names):
    imports = [
        f"import HurtadoZeta23.V26R2MembershipDispatchDiscard{i:02d}Generated"
        for i in range(len(names))
    ]
    rcases = " | ".join(f"hd{i:02d}" for i in range(len(names)))
    calls = "\n".join(
        f"  · exact v26_E3_R2_membership_no_bad_chunk_{i:02d} w hd{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(names))
    )
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- No strict counterexample can carry any of the exact 18 R2 discard codes. -/
theorem v26_E3_R2_membership_no_bad_of_discard_code
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ v26E3R2MembershipDiscardCodes)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [v26E3R2MembershipDiscardCodes, Finset.mem_union] at hw
  rcases hw with {rcases}
{calls}

/-- Package E3 round R2: every strict counterexample in Round2 belongs to the
exact published five-word Round3 table. -/
theorem v26_E3_R2_reduce_23_to_5_membership
    (w : V26BasinWord)
    (hw2 : v26InRound2 w)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26InRound3 w := by
  by_cases hs : v26InRound3 w
  · exact hs
  · have hdiff : v26WordCode w ∈ v26Round2Codes \\ v26Round3Codes :=
      Finset.mem_sdiff.mpr ⟨hw2, hs⟩
    have hd : v26WordCode w ∈ v26E3R2MembershipDiscardCodes := by
      rw [v26_E3_R2_membership_discardCodes_exact]
      exact hdiff
    exact False.elim
      (v26_E3_R2_membership_no_bad_of_discard_code
        w hd g0 g1 g2 g3 g4 g5 hbox hbad)

end HurtadoZeta23
'''


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    _r1, _r2, discards = exact_data()
    base, names, chunks = emit_base(discards)
    files = []

    p = out_dir / "V26R2MembershipDispatchBaseGenerated.lean"
    p.write_text(base, encoding="utf-8")
    files.append(p)

    for i, codes in enumerate(chunks):
        p = out_dir / f"V26R2MembershipDispatchDiscard{i:02d}Generated.lean"
        p.write_text(emit_chunk(i, codes, names[i]), encoding="utf-8")
        files.append(p)

    p = out_dir / "V26R2MembershipDispatchGenerated.lean"
    p.write_text(emit_aggregate(names), encoding="utf-8")
    files.append(p)

    manifest = {
        "round2_codes": 23,
        "discard_codes": 18,
        "survivor_codes": 5,
        "discard_chunks": len(chunks),
        "files": {
            x.name: {
                "bytes": len(x.read_bytes()),
                "sha256": hashlib.sha256(x.read_bytes()).hexdigest(),
            }
            for x in files
        },
    }
    (out_dir / "v26_r2_membership_dispatch_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    m = write(Path(ns.out_dir))
    print("R2 MEMBERSHIP DISPATCH GENERATION OK")
    print("codes:", m["round2_codes"], "=", m["discard_codes"], "+", m["survivor_codes"])
    print("discard chunks:", m["discard_chunks"])


if __name__ == "__main__":
    main()
