#!/usr/bin/env python3
"""Generate the kernel-checkable membership-only R0 router.

The logical content needed from round R0 is only that a strict counterexample
among the 511 Package-D words must lie in the published 231-word Round1 table.
The 21-block R0 contraction boxes are deliberately *not* transported through a
231-way generic match here.  They remain available as concrete per-word
certificates and are reconstructed locally by the next round after its Nat
code has identified the word.

This avoids a large definitional-normalization bottleneck while preserving the
same exact rational certificates and the same reduction 511 -> 231.
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
    survivors, discards = v.run_round(words511, initial=True)
    assert len(words511) == 511
    assert len(survivors) == 231
    assert len(discards) == 280
    scodes = {wcode(x[0]) for x in survivors}
    dcodes = {wcode(x[0]) for x in discards}
    assert scodes.isdisjoint(dcodes)
    assert scodes | dcodes == {wcode(w) for w, _ in words511}
    return words511, survivors, discards


def emit_base(discards):
    dcodes = [wcode(x[0]) for x in discards]
    chunks = [dcodes[i:i + CHUNK] for i in range(0, len(dcodes), CHUNK)]
    names = [f"v26E3R0MembershipDiscardChunk{i:02d}" for i in range(len(chunks))]
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

/-- Exact union of the 280 R0 discard codes. -/
def v26E3R0MembershipDiscardCodes : Finset Nat :=
  {union_expr(names)}

/-- The 280 explicit R0 discard codes are exactly the complement of Round1
inside the 511 Package-D word-code image. -/
theorem v26_E3_R0_membership_discardCodes_exact :
    v26E3R0MembershipDiscardCodes =
      (v26SurvivorWords.image v26WordCode) \\ v26Round1Codes := by
  decide

end HurtadoZeta23
''', names, chunks


def emit_chunk(idx: int, codes: list[str], name: str) -> str:
    branches = []
    for j, code in enumerate(codes):
        branches.append(f'''  · have hcode : v26WordCode w = {code} := hcode{j}
    have hwEq : w = v26E3R0Word_{code} := by
      apply v26_wordCode_injective
      simpa [v26E3R0Word_{code}, v26WordCode] using hcode
    rw [hwEq] at hbox
    exact v26_E3_R0_no_counterexample_{code}
      g0 g1 g2 g3 g4 g5 hbox hbad''')
    rcases = " | ".join(f"hcode{i}" for i in range(len(codes)))
    return f'''import HurtadoZeta23.V26R0MembershipDispatchBaseGenerated
import HurtadoZeta23.V26R0AnalyticDiscards{idx:02d}Generated

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- A strict counterexample cannot have an R0 discard code in chunk {idx}. -/
theorem v26_E3_R0_membership_no_bad_chunk_{idx:02d}
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
        f"import HurtadoZeta23.V26R0MembershipDispatchDiscard{i:02d}Generated"
        for i in range(len(names))
    ]
    rcases = " | ".join(f"hd{i:02d}" for i in range(len(names)))
    calls = "\n".join(
        f"  · exact v26_E3_R0_membership_no_bad_chunk_{i:02d} w hd{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(names))
    )
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- No strict counterexample can carry any of the exact 280 R0 discard codes. -/
theorem v26_E3_R0_membership_no_bad_of_discard_code
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ v26E3R0MembershipDiscardCodes)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [v26E3R0MembershipDiscardCodes, Finset.mem_union] at hw
  rcases hw with {rcases}
{calls}

/-- Package E3 round R0: every strict counterexample among the 511 Package-D
words belongs to the exact published 231-word Round1 table. -/
theorem v26_E3_R0_reduce_511_to_231_membership
    (w : V26BasinWord)
    (hmem : w ∈ v26SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26InRound1 w := by
  by_cases hs : v26InRound1 w
  · exact hs
  · have h511 : v26WordCode w ∈ v26SurvivorWords.image v26WordCode :=
      Finset.mem_image.mpr ⟨w, hmem, rfl⟩
    have hdiff : v26WordCode w ∈
        (v26SurvivorWords.image v26WordCode) \\ v26Round1Codes :=
      Finset.mem_sdiff.mpr ⟨h511, hs⟩
    have hd : v26WordCode w ∈ v26E3R0MembershipDiscardCodes := by
      rw [v26_E3_R0_membership_discardCodes_exact]
      exact hdiff
    exact False.elim
      (v26_E3_R0_membership_no_bad_of_discard_code
        w hd g0 g1 g2 g3 g4 g5 hbox hbad)

end HurtadoZeta23
'''


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    _words511, _survivors, discards = exact_data()
    base, names, chunks = emit_base(discards)
    files = []

    p = out_dir / "V26R0MembershipDispatchBaseGenerated.lean"
    p.write_text(base, encoding="utf-8")
    files.append(p)

    for i, codes in enumerate(chunks):
        p = out_dir / f"V26R0MembershipDispatchDiscard{i:02d}Generated.lean"
        p.write_text(emit_chunk(i, codes, names[i]), encoding="utf-8")
        files.append(p)

    p = out_dir / "V26R0MembershipDispatchGenerated.lean"
    p.write_text(emit_aggregate(names), encoding="utf-8")
    files.append(p)

    manifest = {
        "package_d_codes": 511,
        "discard_codes": 280,
        "survivor_codes": 231,
        "discard_chunks": len(chunks),
        "files": {
            x.name: {
                "bytes": len(x.read_bytes()),
                "sha256": hashlib.sha256(x.read_bytes()).hexdigest(),
            }
            for x in files
        },
    }
    (out_dir / "v26_r0_membership_dispatch_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    m = write(Path(ns.out_dir))
    print("R0 MEMBERSHIP DISPATCH GENERATION OK")
    print("codes:", m["package_d_codes"], "=", m["discard_codes"], "+", m["survivor_codes"])
    print("discard chunks:", m["discard_chunks"])


if __name__ == "__main__":
    main()
