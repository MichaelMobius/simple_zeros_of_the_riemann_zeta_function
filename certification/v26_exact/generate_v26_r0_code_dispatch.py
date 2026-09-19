#!/usr/bin/env python3
"""Generate the kernel-checkable Nat-code dispatch for Package-E3 round R0.

The analytic work is already carried by per-word discard and survivor modules.
This layer performs only finite bookkeeping, but deliberately does it on the
published decimal Nat codes rather than on quantified product words:

* the 511 Package-D codes are `v26SurvivorWords.image v26WordCode`;
* the 231 survivor codes are exactly the published `v26Round1Codes`;
* the remaining 280 codes are the set difference;
* `v26_wordCode_injective` recovers the unique concrete word inside each
  dispatch chunk.

All closed code-table equalities are ordinary kernel `decide`; `native_decide`
is never used.
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
SURVIVOR_CHUNK = 10


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
    survivors, discards = v.run_round(words511, initial=True)
    assert len(words511) == 511
    assert len(survivors) == 231
    assert len(discards) == 280
    survivor_words = [x[0] for x in survivors]
    discard_words = [x[0] for x in discards]
    assert set(survivor_words).isdisjoint(set(discard_words))
    assert set(survivor_words) | set(discard_words) == {w for w, _wt in words511}
    return words511, survivors, discards


def contracted_prop(contracted) -> str:
    parts = []
    for r in range(1, 7):
        for i in range(7 - r):
            L, U = contracted[(i, r)]
            s = bsum(i, r)
            parts.append(f"({ql(L)} ≤ ({s}) ∧ ({s}) ≤ {ql(U)})")
    assert len(parts) == 21
    return " ∧\n      ".join(parts)


def emit_base(survivors, discards):
    scodes = [wcode(x[0]) for x in survivors]
    dcodes = [wcode(x[0]) for x in discards]
    schunks = [scodes[i:i + SURVIVOR_CHUNK] for i in range(0, len(scodes), SURVIVOR_CHUNK)]
    dchunks = [dcodes[i:i + DISCARD_CHUNK] for i in range(0, len(dcodes), DISCARD_CHUNK)]
    snames = [f"v26E3R0SurvivorCodeChunk{i:02d}" for i in range(len(schunks))]
    dnames = [f"v26E3R0DiscardCodeChunk{i:02d}" for i in range(len(dchunks))]

    defs = []
    for name, codes in zip(snames, schunks):
        defs.append(f"def {name} : Finset Nat := {code_finset(codes)}")
    for name, codes in zip(dnames, dchunks):
        defs.append(f"def {name} : Finset Nat := {code_finset(codes)}")

    match_lines = []
    for word, contracted, _qmin, _nused in survivors:
        wc = wcode(word)
        match_lines.append(f"  | {wc} =>\n      {contracted_prop(contracted)}")
    match_lines.append("  | _ => False")

    src = f'''import HurtadoZeta23.V26BasinInterface
import HurtadoZeta23.V26BootstrapStageLists
import HurtadoZeta23.V26WordCodeInjective
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section
namespace HurtadoZeta23

{chr(10).join(defs)}

/-- Literal routing union of all 231 R0-survivor decimal codes. -/
def v26E3R0SurvivorCodes : Finset Nat :=
  {union_expr(snames)}

/-- Literal routing union of all 280 R0-discard decimal codes. -/
def v26E3R0DiscardCodes : Finset Nat :=
  {union_expr(dnames)}

/-- Generic exact contracted box indexed only by the published decimal code. -/
def v26E3R0ContractedBox (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ) : Prop :=
  match v26WordCode w with
{chr(10).join(match_lines)}

/-- The literal 231-code routing union is exactly the published Round1 table. -/
theorem v26_E3_R0_survivorCodes_eq_round1 :
    v26E3R0SurvivorCodes = v26Round1Codes := by
  decide

/-- The literal 280-code routing union is exactly the complement of Round1
inside the 511 Package-D code image. -/
theorem v26_E3_R0_discardCodes_exact :
    v26E3R0DiscardCodes =
      (v26SurvivorWords.image v26WordCode) \\ v26Round1Codes := by
  decide

end HurtadoZeta23
'''
    return src, snames, dnames, schunks, dchunks


def code_to_word_eq(code: str, word_def: str) -> str:
    return f'''    have hwEq : w = {word_def} := by
      apply v26_wordCode_injective
      simpa [{word_def}, v26WordCode] using hcode
    subst w'''


def emit_discard_chunk(idx: int, codes: list[str], chunk_name: str) -> str:
    cases = []
    for code in codes:
        cases.append(f'''  · {code_to_word_eq(code, f"v26E3R0Word_{code}").lstrip()}
    exact v26_E3_R0_no_counterexample_{code}
      g0 g1 g2 g3 g4 g5 hbox hbad''')
    rcases = " | ".join(f"hcode{i}" for i in range(len(codes)))
    branch_text = []
    for i, body in enumerate(cases):
        branch_text.append(body.replace(
            "have hwEq",
            f"have hcode : v26WordCode w = {codes[i]} := hcode{i}\n    have hwEq",
            1,
        ))
    return f'''import HurtadoZeta23.V26R0CodeDispatchBaseGenerated
import HurtadoZeta23.V26R0AnalyticDiscards{idx:02d}Generated

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- Nat-code dispatch over R0 discarded chunk {idx}. -/
theorem v26_E3_R0_no_bad_discard_code_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ {chunk_name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [{chunk_name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(branch_text)}

end HurtadoZeta23
'''


def emit_survivor_chunk(idx: int, items, codes: list[str], chunk_name: str) -> str:
    imports = ["import HurtadoZeta23.V26R0CodeDispatchBaseGenerated"]
    branches = []
    for j, ((word, _contracted, _qmin, _nused), code) in enumerate(zip(items, codes)):
        assert wcode(word) == code
        imports.append(f"import HurtadoZeta23.V26R0Survivor{code}Generated")
        branches.append(f'''  · have hcode : v26WordCode w = {code} := hcode{j}
    have hwEq : w = v26E3R0_{code}Word := by
      apply v26_wordCode_injective
      simpa [v26E3R0_{code}Word, v26WordCode] using hcode
    rw [hwEq] at hbox ⊢
    have hc := v26_E3_R0_{code}_contract_all g0 g1 g2 g3 g4 g5 hbox hbad
    simpa [v26E3R0ContractedBox, v26E3R0_{code}Word,
      v26E3R0_{code}ContractedBox, v26WordCode] using hc''')
    rcases = " | ".join(f"hcode{i}" for i in range(len(codes)))
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- Nat-code dispatch over R0 survivor chunk {idx}. -/
theorem v26_E3_R0_contract_survivor_code_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : v26WordCode w ∈ {chunk_name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  simp only [{chunk_name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(branches)}

end HurtadoZeta23
'''


def emit_aggregate(snames, dnames):
    imports = [
        f"import HurtadoZeta23.V26R0CodeDispatchDiscard{i:02d}Generated"
        for i in range(len(dnames))
    ]
    imports += [
        f"import HurtadoZeta23.V26R0CodeDispatchSurvivor{i:02d}Generated"
        for i in range(len(snames))
    ]
    d_rcases = " | ".join(f"hd{i:02d}" for i in range(len(dnames)))
    d_calls = "\n".join(
        f"  · exact v26_E3_R0_no_bad_discard_code_chunk_{i:02d} w hd{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(dnames))
    )
    s_rcases = " | ".join(f"hs{i:02d}" for i in range(len(snames)))
    s_calls = "\n".join(
        f"  · exact v26_E3_R0_contract_survivor_code_chunk_{i:02d} w hs{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(snames))
    )
    return f'''{chr(10).join(imports)}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace HurtadoZeta23

/-- No strict counterexample can have one of the exact 280 R0 discard codes. -/
theorem v26_E3_R0_no_bad_of_discard_code
    (w : V26BasinWord) (hw : v26WordCode w ∈ v26E3R0DiscardCodes)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [v26E3R0DiscardCodes, Finset.mem_union] at hw
  rcases hw with {d_rcases}
{d_calls}

/-- Every strict counterexample with a published Round1 code satisfies its exact
R0-contracted 21-block box. -/
theorem v26_E3_R0_contract_of_round1_code
    (w : V26BasinWord) (hw : v26InRound1 w)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  have hs : v26WordCode w ∈ v26E3R0SurvivorCodes := by
    rw [v26_E3_R0_survivorCodes_eq_round1]
    exact hw
  simp only [v26E3R0SurvivorCodes, Finset.mem_union] at hs
  rcases hs with {s_rcases}
{s_calls}

/-- Package E3 round R0, aggregated entirely through Nat code tables. -/
theorem v26_E3_R0_reduce_511_to_231
    (w : V26BasinWord) (hmem : w ∈ v26SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26InRound1 w ∧
      v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  by_cases hs : v26InRound1 w
  · exact ⟨hs, v26_E3_R0_contract_of_round1_code
      w hs g0 g1 g2 g3 g4 g5 hbox hbad⟩
  · have h511 : v26WordCode w ∈ v26SurvivorWords.image v26WordCode := by
      exact Finset.mem_image.mpr ⟨w, hmem, rfl⟩
    have hnot : v26WordCode w ∉ v26Round1Codes := hs
    have hdiff : v26WordCode w ∈
        (v26SurvivorWords.image v26WordCode) \\ v26Round1Codes :=
      Finset.mem_sdiff.mpr ⟨h511, hnot⟩
    have hd : v26WordCode w ∈ v26E3R0DiscardCodes := by
      rw [v26_E3_R0_discardCodes_exact]
      exact hdiff
    exact False.elim
      (v26_E3_R0_no_bad_of_discard_code
        w hd g0 g1 g2 g3 g4 g5 hbox hbad)

end HurtadoZeta23
'''


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    _words511, survivors, discards = exact_data()
    base, snames, dnames, schunks, dchunks = emit_base(survivors, discards)
    files = []
    p = out_dir / "V26R0CodeDispatchBaseGenerated.lean"
    p.write_text(base, encoding="utf-8")
    files.append(p)

    for i, codes in enumerate(dchunks):
        p = out_dir / f"V26R0CodeDispatchDiscard{i:02d}Generated.lean"
        p.write_text(emit_discard_chunk(i, codes, dnames[i]), encoding="utf-8")
        files.append(p)

    sitems = [
        survivors[i:i + SURVIVOR_CHUNK]
        for i in range(0, len(survivors), SURVIVOR_CHUNK)
    ]
    for i, (items, codes) in enumerate(zip(sitems, schunks)):
        p = out_dir / f"V26R0CodeDispatchSurvivor{i:02d}Generated.lean"
        p.write_text(emit_survivor_chunk(i, items, codes, snames[i]), encoding="utf-8")
        files.append(p)

    p = out_dir / "V26R0CodeDispatchGenerated.lean"
    p.write_text(emit_aggregate(snames, dnames), encoding="utf-8")
    files.append(p)

    manifest = {
        "package_d_codes": 511,
        "discard_codes": 280,
        "survivor_codes": 231,
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
    (out_dir / "v26_r0_code_dispatch_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    m = write(Path(ns.out_dir))
    print("R0 NAT-CODE DISPATCH GENERATION OK")
    print("codes:", m["package_d_codes"], "=", m["discard_codes"], "+", m["survivor_codes"])
    print("discard chunks:", m["discard_chunks"])
    print("survivor chunks:", m["survivor_chunks"])


if __name__ == "__main__":
    main()
