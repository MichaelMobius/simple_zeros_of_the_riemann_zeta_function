#!/usr/bin/env python3
"""Generate the kernel-checkable Nat-code router for Package-E3 round R1.

R1 starts from the 231 R0 survivors with their exact R0-contracted boxes.
The historical exact bootstrap leaves 23 words and discards 208.  This layer
contains no new analysis: it only routes the already kernel-checked concrete
R1 discard and survivor-contraction certificates by the published decimal
word code.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json

import generate_v26_bootstrap_lean as boot

v = boot.v
DISCARD_CHUNK = 10
SURVIVOR_CHUNK = 8


def ql(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def wcode(w) -> str:
    return "".join(map(str, w))


def bsum(i: int, r: int) -> str:
    return " + ".join(f"g{j}" for j in range(i, i + r))


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
    assert len(r0) == 231 and len(d0) == 280
    assert len(r1) == 23 and len(d1) == 208
    scodes = {wcode(x[0]) for x in r1}
    dcodes = {wcode(x[0]) for x in d1}
    assert scodes.isdisjoint(dcodes)
    assert scodes | dcodes == {wcode(x[0]) for x in r0}
    return r0, r1, d1


def contracted_prop(contracted) -> str:
    pieces = []
    for r in range(1, 7):
        for i in range(7 - r):
            L, U = contracted[(i, r)]
            s = bsum(i, r)
            pieces.append(f"({ql(L)} ≤ ({s}) ∧ ({s}) ≤ {ql(U)})")
    assert len(pieces) == 21
    return " ∧\n      ".join(pieces)


def emit_base(r1, d1):
    scodes = [wcode(x[0]) for x in r1]
    dcodes = [wcode(x[0]) for x in d1]
    schunks = [scodes[i:i + SURVIVOR_CHUNK] for i in range(0, len(scodes), SURVIVOR_CHUNK)]
    dchunks = [dcodes[i:i + DISCARD_CHUNK] for i in range(0, len(dcodes), DISCARD_CHUNK)]
    snames = [f"v26E3R1SurvivorCodeChunk{i:02d}" for i in range(len(schunks))]
    dnames = [f"v26E3R1DiscardCodeChunk{i:02d}" for i in range(len(dchunks))]

    defs = []
    for name, codes in zip(snames, schunks):
        defs.append(f"def {name} : Finset Nat := {code_finset(codes)}")
    for name, codes in zip(dnames, dchunks):
        defs.append(f"def {name} : Finset Nat := {code_finset(codes)}")

    match_lines = []
    for word, contracted, _qmin, _nused in r1:
        code = wcode(word)
        match_lines.append(f"  | {code} =>\n      {contracted_prop(contracted)}")
    match_lines.append("  | _ => False")

    src = f'''import HurtadoZeta23.V26R0CodeDispatchBaseGenerated
import HurtadoZeta23.V26BootstrapStageLists
import HurtadoZeta23.V26WordCodeInjective
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section
namespace HurtadoZeta23

{chr(10).join(defs)}

/-- Literal union of the exact 23 R1 survivor codes. -/
def v26E3R1SurvivorCodes : Finset Nat :=
  {union_expr(snames)}

/-- Literal union of the exact 208 R1 discard codes. -/
def v26E3R1DiscardCodes : Finset Nat :=
  {union_expr(dnames)}

/-- Generic exact R1-contracted box, indexed only by decimal word code. -/
def v26E3R1ContractedBox (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ) : Prop :=
  match v26WordCode w with
{chr(10).join(match_lines)}

/-- The literal 23-code survivor union is exactly the published Round2 table. -/
theorem v26_E3_R1_survivorCodes_eq_round2 :
    v26E3R1SurvivorCodes = v26Round2Codes := by
  decide

/-- The literal 208-code discard union is exactly Round1 minus Round2. -/
theorem v26_E3_R1_discardCodes_exact :
    v26E3R1DiscardCodes = v26Round1Codes \\ v26Round2Codes := by
  decide

end HurtadoZeta23
'''
    return src, snames, dnames, schunks, dchunks


def emit_discard_chunk(idx: int, codes: list[str], chunk_name: str) -> str:
    branches = []
    for j, code in enumerate(codes):
        branches.append(f'''  · have hcode : v26WordCode w = {code} := hcode{j}
    have hwEq : w = v26E3R0_{code}Word := by
      apply v26_wordCode_injective
      simpa [v26E3R0_{code}Word, v26WordCode] using hcode
    rw [hwEq] at hbox
    have hconcrete : v26E3R0_{code}ContractedBox g0 g1 g2 g3 g4 g5 := by
      simpa [v26E3R0ContractedBox, v26E3R0_{code}Word,
        v26E3R0_{code}ContractedBox, v26WordCode] using hbox
    exact (v26_E3_R1_no_counterexample_{code}
      g0 g1 g2 g3 g4 g5 hconcrete) hbad''')
    rcases = " | ".join(f"hcode{i}" for i in range(len(codes)))
    return f'''import HurtadoZeta23.V26R1CodeDispatchBaseGenerated
import HurtadoZeta23.V26R1AnalyticDiscards{idx:02d}Generated

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- Nat-code routing over R1 discarded chunk {idx}. -/
theorem v26_E3_R1_no_bad_discard_code_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ {chunk_name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [{chunk_name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(branches)}

end HurtadoZeta23
'''


def emit_survivor_chunk(idx: int, items, codes: list[str], chunk_name: str) -> str:
    imports = ["import HurtadoZeta23.V26R1CodeDispatchBaseGenerated"]
    branches = []
    for j, ((word, _contracted, _qmin, _nused), code) in enumerate(zip(items, codes)):
        assert wcode(word) == code
        imports.append(f"import HurtadoZeta23.V26R1Survivor{code}Generated")
        branches.append(f'''  · have hcode : v26WordCode w = {code} := hcode{j}
    have hwEq : w = v26E3R0_{code}Word := by
      apply v26_wordCode_injective
      simpa [v26E3R0_{code}Word, v26WordCode] using hcode
    rw [hwEq] at hbox ⊢
    have hconcrete : v26E3R0_{code}ContractedBox g0 g1 g2 g3 g4 g5 := by
      simpa [v26E3R0ContractedBox, v26E3R0_{code}Word,
        v26E3R0_{code}ContractedBox, v26WordCode] using hbox
    have hc := v26_E3_R1_{code}_contract_all
      g0 g1 g2 g3 g4 g5 hconcrete hbad
    simpa [v26E3R1ContractedBox, v26E3R0_{code}Word,
      v26E3R1_{code}ContractedBox, v26WordCode] using hc''')
    rcases = " | ".join(f"hcode{i}" for i in range(len(codes)))
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- Nat-code routing over R1 survivor chunk {idx}. -/
theorem v26_E3_R1_contract_survivor_code_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ {chunk_name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26E3R1ContractedBox w g0 g1 g2 g3 g4 g5 := by
  simp only [{chunk_name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(branches)}

end HurtadoZeta23
'''


def emit_aggregate(snames, dnames):
    imports = [
        f"import HurtadoZeta23.V26R1CodeDispatchDiscard{i:02d}Generated"
        for i in range(len(dnames))
    ]
    imports += [
        f"import HurtadoZeta23.V26R1CodeDispatchSurvivor{i:02d}Generated"
        for i in range(len(snames))
    ]
    d_rcases = " | ".join(f"hd{i:02d}" for i in range(len(dnames)))
    d_calls = "\n".join(
        f"  · exact v26_E3_R1_no_bad_discard_code_chunk_{i:02d} w hd{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(dnames))
    )
    s_rcases = " | ".join(f"hs{i:02d}" for i in range(len(snames)))
    s_calls = "\n".join(
        f"  · exact v26_E3_R1_contract_survivor_code_chunk_{i:02d} w hs{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(snames))
    )
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- No strict counterexample can carry one of the exact 208 R1 discard codes. -/
theorem v26_E3_R1_no_bad_of_discard_code
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ v26E3R1DiscardCodes)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [v26E3R1DiscardCodes, Finset.mem_union] at hw
  rcases hw with {d_rcases}
{d_calls}

/-- Every strict counterexample with a Round2 code reaches its exact R1 box. -/
theorem v26_E3_R1_contract_of_round2_code
    (w : V26BasinWord) (hw : v26InRound2 w)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26E3R1ContractedBox w g0 g1 g2 g3 g4 g5 := by
  have hs : v26WordCode w ∈ v26E3R1SurvivorCodes := by
    rw [v26_E3_R1_survivorCodes_eq_round2]
    exact hw
  simp only [v26E3R1SurvivorCodes, Finset.mem_union] at hs
  rcases hs with {s_rcases}
{s_calls}

/-- Package E3 round R1: exact reduction from 231 R0 survivors to 23 R1 survivors. -/
theorem v26_E3_R1_reduce_231_to_23
    (w : V26BasinWord) (hw1 : v26InRound1 w)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26InRound2 w ∧ v26E3R1ContractedBox w g0 g1 g2 g3 g4 g5 := by
  by_cases hs : v26InRound2 w
  · exact ⟨hs, v26_E3_R1_contract_of_round2_code
      w hs g0 g1 g2 g3 g4 g5 hbox hbad⟩
  · have hdiff : v26WordCode w ∈ v26Round1Codes \\ v26Round2Codes :=
      Finset.mem_sdiff.mpr ⟨hw1, hs⟩
    have hd : v26WordCode w ∈ v26E3R1DiscardCodes := by
      rw [v26_E3_R1_discardCodes_exact]
      exact hdiff
    exact False.elim
      (v26_E3_R1_no_bad_of_discard_code
        w hd g0 g1 g2 g3 g4 g5 hbox hbad)

end HurtadoZeta23
'''


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    _r0, r1, d1 = exact_data()
    base, snames, dnames, schunks, dchunks = emit_base(r1, d1)
    files = []

    p = out_dir / "V26R1CodeDispatchBaseGenerated.lean"
    p.write_text(base, encoding="utf-8")
    files.append(p)

    for i, codes in enumerate(dchunks):
        p = out_dir / f"V26R1CodeDispatchDiscard{i:02d}Generated.lean"
        p.write_text(emit_discard_chunk(i, codes, dnames[i]), encoding="utf-8")
        files.append(p)

    sitems = [r1[i:i + SURVIVOR_CHUNK] for i in range(0, len(r1), SURVIVOR_CHUNK)]
    for i, (items, codes) in enumerate(zip(sitems, schunks)):
        p = out_dir / f"V26R1CodeDispatchSurvivor{i:02d}Generated.lean"
        p.write_text(emit_survivor_chunk(i, items, codes, snames[i]), encoding="utf-8")
        files.append(p)

    p = out_dir / "V26R1CodeDispatchGenerated.lean"
    p.write_text(emit_aggregate(snames, dnames), encoding="utf-8")
    files.append(p)

    manifest = {
        "round1_codes": 231,
        "discard_codes": 208,
        "survivor_codes": 23,
        "discard_chunks": len(dchunks),
        "survivor_chunks": len(schunks),
        "files": {
            x.name: {
                "bytes": len(x.read_bytes()),
                "sha256": hashlib.sha256(x.read_bytes()).hexdigest(),
            }
            for x in files
        },
    }
    (out_dir / "v26_r1_code_dispatch_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    m = write(Path(ns.out_dir))
    print("R1 NAT-CODE DISPATCH GENERATION OK")
    print("codes:", m["round1_codes"], "=", m["discard_codes"], "+", m["survivor_codes"])
    print("discard chunks:", m["discard_chunks"])
    print("survivor chunks:", m["survivor_chunks"])


if __name__ == "__main__":
    main()
