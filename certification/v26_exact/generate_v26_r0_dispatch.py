#!/usr/bin/env python3
"""Generate the kernel-checkable Package-E3 R0 dispatch layer.

This layer turns the per-word R0 certificates into one theorem about an
arbitrary Package-D counterexample word:

    511 Package-D survivors -> 231 R0 survivors + exact contracted box.

No analytic inequality is recomputed here.  The generator only serializes the
exact finite partition supplied by the Fraction-only verifier and dispatches
to already kernel-checked per-word discard/contraction theorems.  The finite
511 = 280 + 231 partition is itself checked by ordinary `decide` in Lean;
`native_decide` is deliberately not used.
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


def word_value(w) -> str:
    tys = [7, 5, 6, 6, 5, 7]
    vals = [d - 1 for d in w]
    return "(" + ", ".join(f"({a} : Fin {n})" for a, n in zip(vals, tys)) + ")"


def bsum(i: int, r: int) -> str:
    return " + ".join(f"g{j}" for j in range(i, i + r))


def finset_literal(words) -> str:
    assert words
    return "{" + ", ".join(word_value(w) for w in words) + "}"


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


def emit_base(survivors, discards) -> tuple[str, list[str], list[str]]:
    survivor_words = [x[0] for x in survivors]
    discard_words = [x[0] for x in discards]
    schunks = [survivor_words[i:i + SURVIVOR_CHUNK]
               for i in range(0, len(survivor_words), SURVIVOR_CHUNK)]
    dchunks = [discard_words[i:i + DISCARD_CHUNK]
               for i in range(0, len(discard_words), DISCARD_CHUNK)]
    snames = [f"v26E3R0SurvivorChunk{i:02d}" for i in range(len(schunks))]
    dnames = [f"v26E3R0DiscardChunk{i:02d}" for i in range(len(dchunks))]

    chunk_defs = []
    for name, words in zip(snames, schunks):
        chunk_defs.append(
            f"def {name} : Finset V26BasinWord := {finset_literal(words)}")
    for name, words in zip(dnames, dchunks):
        chunk_defs.append(
            f"def {name} : Finset V26BasinWord := {finset_literal(words)}")

    match_lines = []
    for word, contracted, _qmin, _nused in survivors:
        pat = ", ".join(str(d - 1) for d in word)
        match_lines.append(f"  | {pat} =>\n      {contracted_prop(contracted)}")
    match_lines.append("  | _, _, _, _, _, _ => False")

    src = f'''import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

{chr(10).join(chunk_defs)}

/-- The exact 231 words surviving the first rational bootstrap round. -/
def v26E3R0SurvivorWords : Finset V26BasinWord :=
  {union_expr(snames)}

/-- The exact 280 Package-D words discarded by the first rational round. -/
def v26E3R0DiscardWords : Finset V26BasinWord :=
  {union_expr(dnames)}

/-- Exact contracted 21-block box attached to each of the 231 R0 survivors.
The fallback is `False`, so membership outside the 231-word table carries no
spurious box information. -/
def v26E3R0ContractedBox (w : V26BasinWord)
    (g0 g1 g2 g3 g4 g5 : ℝ) : Prop :=
  match w.1.val, w.2.1.val, w.2.2.1.val, w.2.2.2.1.val,
      w.2.2.2.2.1.val, w.2.2.2.2.2.val with
{chr(10).join(match_lines)}

/-- Kernel-reducible exact R0 partition of the 511 Package-D words. -/
theorem v26_E3_R0_partition_511 :
    v26SurvivorWords = v26E3R0DiscardWords ∪ v26E3R0SurvivorWords := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide

/-- Exact cardinality certificate for the discarded side of R0. -/
theorem v26_E3_R0_discard_count : v26E3R0DiscardWords.card = 280 := by
  set_option maxHeartbeats 0 in
  decide

/-- Exact cardinality certificate for the surviving side of R0. -/
theorem v26_E3_R0_survivor_count : v26E3R0SurvivorWords.card = 231 := by
  set_option maxHeartbeats 0 in
  decide

end HurtadoZeta23
'''
    return src, snames, dnames


def emit_discard_chunk(idx: int, words, chunk_name: str) -> str:
    cases = []
    for word in words:
        wc = wcode(word)
        cases.append(f'''  · have hnb := v26_E3_R0_no_counterexample_{wc}
      g0 g1 g2 g3 g4 g5
      (by simpa [v26E3R0Word_{wc}] using hbox)
    exact hnb hbad''')
    rcases = " | ".join("rfl" for _ in words)
    return f'''import HurtadoZeta23.V26R0DispatchBaseGenerated
import HurtadoZeta23.V26R0AnalyticDiscards{idx:02d}Generated

namespace HurtadoZeta23

/-- Dispatch over R0 discarded chunk {idx}. -/
theorem v26_E3_R0_no_bad_discard_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : w ∈ {chunk_name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [{chunk_name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(cases)}

end HurtadoZeta23
'''


def emit_survivor_chunk(idx: int, items, chunk_name: str) -> str:
    imports = ["import HurtadoZeta23.V26R0DispatchBaseGenerated"]
    cases = []
    for word, contracted, _qmin, _nused in items:
        wc = wcode(word)
        imports.append(f"import HurtadoZeta23.V26R0Survivor{wc}Generated")
        prop = contracted_prop(contracted)
        cases.append(f'''  · change {prop}
    have hc := v26_E3_R0_{wc}_contract_all g0 g1 g2 g3 g4 g5
      (by simpa [v26E3R0_{wc}Word] using hbox) hbad
    simpa [v26E3R0_{wc}ContractedBox] using hc''')
    rcases = " | ".join("rfl" for _ in items)
    return f'''{chr(10).join(imports)}

namespace HurtadoZeta23

/-- Dispatch over R0 survivor chunk {idx}; every member receives its exact
historical 21-block contracted box. -/
theorem v26_E3_R0_contract_survivor_chunk_{idx:02d}
    (w : V26BasinWord)
    (hw : w ∈ {chunk_name})
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  simp only [{chunk_name}, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with {rcases}
{chr(10).join(cases)}

end HurtadoZeta23
'''


def emit_aggregate(snames: list[str], dnames: list[str]) -> str:
    imports = [f"import HurtadoZeta23.V26R0DispatchDiscard{i:02d}Generated"
               for i in range(len(dnames))]
    imports += [f"import HurtadoZeta23.V26R0DispatchSurvivor{i:02d}Generated"
                for i in range(len(snames))]
    d_rcases = " | ".join(f"hd{i:02d}" for i in range(len(dnames)))
    d_calls = "\n".join(
        f"  · exact v26_E3_R0_no_bad_discard_chunk_{i:02d} w hd{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(dnames)))
    s_rcases = " | ".join(f"hs{i:02d}" for i in range(len(snames)))
    s_calls = "\n".join(
        f"  · exact v26_E3_R0_contract_survivor_chunk_{i:02d} w hs{i:02d} g0 g1 g2 g3 g4 g5 hbox hbad"
        for i in range(len(snames)))
    return f'''{chr(10).join(imports)}

namespace HurtadoZeta23

/-- No strict counterexample can lie in the exact 280-word R0 discard set. -/
theorem v26_E3_R0_no_bad_of_mem_discard
    (w : V26BasinWord) (hw : w ∈ v26E3R0DiscardWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  simp only [v26E3R0DiscardWords, Finset.mem_union] at hw
  rcases hw with {d_rcases}
{d_calls}

/-- Every strict counterexample whose word is one of the 231 R0 survivors lies
in that word's exact contracted 21-block box. -/
theorem v26_E3_R0_contract_of_mem_survivor
    (w : V26BasinWord) (hw : w ∈ v26E3R0SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  simp only [v26E3R0SurvivorWords, Finset.mem_union] at hw
  rcases hw with {s_rcases}
{s_calls}

/-- Package E3 round R0, aggregated: an arbitrary Package-D 511-word strict
counterexample cannot be one of the 280 discarded words, hence belongs to the
exact 231-word survivor set and satisfies its exact contracted 21-block box. -/
theorem v26_E3_R0_reduce_511_to_231
    (w : V26BasinWord) (hmem : w ∈ v26SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    w ∈ v26E3R0SurvivorWords ∧
      v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  have hp : w ∈ v26E3R0DiscardWords ∪ v26E3R0SurvivorWords := by
    rw [← v26_E3_R0_partition_511]
    exact hmem
  rcases Finset.mem_union.mp hp with hd | hs
  · exact False.elim
      (v26_E3_R0_no_bad_of_mem_discard w hd g0 g1 g2 g3 g4 g5 hbox hbad)
  · exact ⟨hs, v26_E3_R0_contract_of_mem_survivor
      w hs g0 g1 g2 g3 g4 g5 hbox hbad⟩

end HurtadoZeta23
'''


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    _words511, survivors, discards = exact_data()
    base, snames, dnames = emit_base(survivors, discards)
    files = []
    base_path = out_dir / "V26R0DispatchBaseGenerated.lean"
    base_path.write_text(base, encoding="utf-8")
    files.append(base_path)

    dwords = [x[0] for x in discards]
    dchunks = [dwords[i:i + DISCARD_CHUNK]
               for i in range(0, len(dwords), DISCARD_CHUNK)]
    for i, words in enumerate(dchunks):
        path = out_dir / f"V26R0DispatchDiscard{i:02d}Generated.lean"
        path.write_text(emit_discard_chunk(i, words, dnames[i]), encoding="utf-8")
        files.append(path)

    schunks = [survivors[i:i + SURVIVOR_CHUNK]
               for i in range(0, len(survivors), SURVIVOR_CHUNK)]
    for i, items in enumerate(schunks):
        path = out_dir / f"V26R0DispatchSurvivor{i:02d}Generated.lean"
        path.write_text(emit_survivor_chunk(i, items, snames[i]), encoding="utf-8")
        files.append(path)

    agg = out_dir / "V26R0DispatchGenerated.lean"
    agg.write_text(emit_aggregate(snames, dnames), encoding="utf-8")
    files.append(agg)

    manifest = {
        "package_d_words": 511,
        "discard_count": len(discards),
        "survivor_count": len(survivors),
        "discard_chunks": len(dchunks),
        "survivor_chunks": len(schunks),
        "files": {
            p.name: {"bytes": len(p.read_bytes()),
                     "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in files
        },
    }
    (out_dir / "v26_r0_dispatch_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    manifest = write(Path(ns.out_dir))
    print("R0 DISPATCH GENERATION OK")
    print("partition:", manifest["package_d_words"], "=",
          manifest["discard_count"], "+", manifest["survivor_count"])
    print("discard chunks:", manifest["discard_chunks"])
    print("survivor chunks:", manifest["survivor_chunks"])


if __name__ == "__main__":
    main()
