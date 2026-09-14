#!/usr/bin/env python3
"""Normalize generated R0 dispatch to the canonical published Round1 code set.

The first dispatch draft certified one large literal Finset equality
`511 = 280 ∪ 231`.  That creates an unnecessarily deep theorem statement.
Package D already contains the published 231-code table `v26Round1Codes` and
its predicate `v26InRound1`.  This normalizer keeps literal chunk Finsets only
for routing to per-word theorems, but replaces the large partition theorem by
two small closed finite propositions:

* literal 231 survivor table <-> `v26InRound1`;
* Package-D 511 membership + not Round1 -> literal 280 discard table.

Both are ordinary kernel `decide`, never `native_decide`.  The aggregate
reduction then returns `v26InRound1 w` as the canonical stage fact.
"""
from pathlib import Path
import argparse
import re

BASE_OLD_RE = re.compile(
    r"/-- Kernel-reducible exact R0 partition of the 511 Package-D words\. -/.*?"
    r"theorem v26_E3_R0_survivor_count.*?\n  decide\n",
    re.S,
)

BASE_NEW = r'''/-- The generated literal 231-word routing table is exactly the published
Round1 code predicate already present in Package D. -/
theorem v26_E3_R0_survivorWords_iff_round1 :
    ∀ w : V26BasinWord,
      (w ∈ v26E3R0SurvivorWords ↔ v26InRound1 w) := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide

/-- If a Package-D 511 survivor is not in the published Round1 code table,
it belongs to the exact generated 280-word discard routing table. -/
theorem v26_E3_R0_discard_of_511_not_round1 :
    ∀ w : V26BasinWord,
      w ∈ v26SurvivorWords →
      ¬ v26InRound1 w →
      w ∈ v26E3R0DiscardWords := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide
'''

AGG_RE = re.compile(
    r"/-- Package E3 round R0, aggregated:.*?"
    r"theorem v26_E3_R0_reduce_511_to_231.*?\n\nend HurtadoZeta23\n",
    re.S,
)

AGG_NEW = r'''/-- Package E3 round R0, aggregated: an arbitrary Package-D 511-word strict
counterexample must lie in the published 231-code Round1 set and satisfies the
exact contracted 21-block box attached to that word. -/
theorem v26_E3_R0_reduce_511_to_231
    (w : V26BasinWord) (hmem : w ∈ v26SurvivorWords)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hbox : v26InWordBox w g0 g1 g2 g3 g4 g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    v26InRound1 w ∧
      v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  by_cases hs : v26InRound1 w
  · have hroute : w ∈ v26E3R0SurvivorWords :=
      (v26_E3_R0_survivorWords_iff_round1 w).2 hs
    exact ⟨hs, v26_E3_R0_contract_of_mem_survivor
      w hroute g0 g1 g2 g3 g4 g5 hbox hbad⟩
  · have hd : w ∈ v26E3R0DiscardWords :=
      v26_E3_R0_discard_of_511_not_round1 w hmem hs
    exact False.elim
      (v26_E3_R0_no_bad_of_mem_discard w hd g0 g1 g2 g3 g4 g5 hbox hbad)

end HurtadoZeta23
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    base = out / "V26R0DispatchBaseGenerated.lean"
    agg = out / "V26R0DispatchGenerated.lean"

    btxt = base.read_text(encoding="utf-8")
    if "import HurtadoZeta23.V26BootstrapStageLists" not in btxt:
        btxt = btxt.replace(
            "import HurtadoZeta23.V26BasinInterface\n",
            "import HurtadoZeta23.V26BasinInterface\n"
            "import HurtadoZeta23.V26BootstrapStageLists\n",
            1,
        )
    btxt2, nbase = BASE_OLD_RE.subn(BASE_NEW, btxt, count=1)
    if nbase != 1:
        raise RuntimeError(f"expected one base partition block, replaced {nbase}")
    base.write_text(btxt2, encoding="utf-8")

    atxt = agg.read_text(encoding="utf-8")
    atxt2, nagg = AGG_RE.subn(AGG_NEW, atxt, count=1)
    if nagg != 1:
        raise RuntimeError(f"expected one aggregate reduction block, replaced {nagg}")
    agg.write_text(atxt2, encoding="utf-8")

    print("R0 DISPATCH STAGE NORMALIZATION OK")
    print("canonical survivor predicate: v26InRound1")


if __name__ == "__main__":
    main()
