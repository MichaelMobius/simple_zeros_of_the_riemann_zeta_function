#!/usr/bin/env python3
"""Generate one kernel-checkable analytic discard bridge for bootstrap round R1.

The pilot selects the first of the 208 historical R1 discards.  Its hypotheses
are the exact 21-block contracted box proved by the corresponding R0 survivor
module.  Every analytic term is discharged by the deduplicated R1 cell catalog,
and the already-generated exact rational R1 discard theorem then excludes a
strict counterexample.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse

import generate_v26_bootstrap_lean as boot
import generate_v26_r1_cell_catalog as catalog

v = boot.v


def ql(x: Q) -> str:
    x = Q(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def wcode(w) -> str:
    return "".join(map(str, w))


def bsum(i: int, r: int) -> str:
    return " + ".join(f"x{j}" for j in range(i, i + r))


def block_name(r: int, i: int) -> str:
    return f"b{r - 1}{i}"


def minor_expr(N: int, alpha: Q, eta: Q, x: str) -> str:
    return f"{ql(alpha)} * (({x}) - v21RootRight {N}) ^ 2 - {ql(eta)}"


def assembled_lower(exprs: list[str]) -> str:
    assert len(exprs) == 21
    p = [f"({e})" for e in exprs]
    pressure = " +\n      ".join(f"v26Pressure {i} * x{i}" for i in range(6))
    return (
        pressure
        + " +\n      (1 / 3 : ℝ) * (" + " + ".join(p[0:6]) + ")"
        + " +\n      (2 / 5 : ℝ) * (" + " + ".join(p[6:11]) + ")"
        + " +\n      (1 / 2 : ℝ) * (" + " + ".join(p[11:15]) + ")"
        + " +\n      (2 / 3 : ℝ) * (" + " + ".join(p[15:18]) + ")"
        + " +\n      " + p[18] + " + " + p[19] + " + 2 * " + p[20]
    )


def pilot_data():
    words511, _ = v.enumerate_511()
    r0, _d0 = v.run_round(words511, initial=True)
    r1, d1 = v.run_round(r0)
    assert len(r0) == 231 and len(r1) == 23 and len(d1) == 208
    word, margin, qmin, nused = d1[0]
    by_word = {tuple(item[0]): item for item in r0}
    r0_item = by_word[tuple(word)]
    intervals = r0_item[1]
    M, b, c, used = v.build_Q(word, intervals)
    qmin2, _inv, _xstar = v.qmin_and_inverse(M, b, c)
    assert qmin2 == qmin and qmin >= v.delta
    assert len(used) == nused
    return word, intervals, used, margin


def emit() -> str:
    word, intervals, used, _margin = pilot_data()
    wc = wcode(word)
    qtxt, _M, _b, _c, used2 = boot.quadratic_expr(word, intervals)
    assert [(a,b,c,d,e) for a,b,c,d,e,_ in used] == [(a,b,c,d,e) for a,b,c,d,e,_ in used2]
    used_by_key = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in used}

    exprs = []
    proofs = []
    hnames = []
    bassign = []
    catalog_modules = set()
    idx21 = 0
    used_count = 0
    for r in range(1, 7):
        for i in range(7 - r):
            s = bsum(i, r)
            hb = f"hb{idx21:02d}"
            if (i, r) in used_by_key:
                N, alpha, eta = used_by_key[(i, r)]
                L, U = intervals[(i, r)]
                key = catalog.cell_key(L, U, N, alpha, eta)
                cell_idx = catalog.CELL_INDEX[key]
                catalog_modules.add(cell_idx // catalog.CHUNK_SIZE)
                expr = minor_expr(N, alpha, eta, s)
                hn = f"hm{idx21:02d}"
                proofs.append(
                    f"  have {hn} := v26_R1_cell_{cell_idx:04d} (x := {s}) {hb}.1 {hb}.2"
                )
                used_count += 1
            else:
                expr = "0"
                hn = f"hm{idx21:02d}"
                proofs.append(f"  have {hn} := v26_limitingWeight_nonneg ({s})")
            exprs.append(expr)
            hnames.append(hn)
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            idx21 += 1
    assert idx21 == 21 and used_count == len(used)

    # Locate the exact rational discard theorem's generated chunk.
    words511, _ = v.enumerate_511()
    r0, _ = v.run_round(words511, initial=True)
    _r1, d1 = v.run_round(r0)
    discard_index = next(i for i, item in enumerate(d1) if tuple(item[0]) == tuple(word))
    bootstrap_chunk = discard_index // boot.CHUNK_SIZE

    imports = [
        f"import HurtadoZeta23.V26BootstrapR1Chunk{bootstrap_chunk}",
        f"import HurtadoZeta23.V26R0Survivor{wc}Generated",
        "import HurtadoZeta23.V26GapBlockLower",
    ]
    imports += [
        f"import HurtadoZeta23.V26R1CellCatalog{m:03d}Generated"
        for m in sorted(catalog_modules)
    ]
    lower = assembled_lower(exprs)
    hb_names = ", ".join(f"hb{i:02d}" for i in range(21))

    return f'''{chr(10).join(imports)}
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- Historical rounded R1 quadratic for the pilot discarded word `{wc}`. -/
def v26E3R1PilotQ (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {qtxt}

/-- Symbolic-root analytic assembly on the exact R0-contracted input box. -/
def v26E3R1PilotAssembled (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {lower}

theorem v26_E3_R1_pilot_Q_eq_assembled
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26E3R1PilotQ x0 x1 x2 x3 x4 x5 =
      v26E3R1PilotAssembled x0 x1 x2 x3 x4 x5 := by
  unfold v26E3R1PilotQ v26E3R1PilotAssembled
  simp [v26Pressure, v21RootRight]
  ring

/-- The pilot R1 assembly is below the actual functional throughout the exact
R0 contracted 21-block box. -/
theorem v26_E3_R1_pilot_assembled_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26E3R0_{wc}ContractedBox x0 x1 x2 x3 x4 x5) :
    v26E3R1PilotAssembled x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  unfold v26E3R0_{wc}ContractedBox at hbox
  rcases hbox with ⟨{hb_names}⟩
{chr(10).join(proofs)}
  unfold v26E3R1PilotAssembled
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(hnames)}

theorem v26_E3_R1_pilot_Q_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26E3R0_{wc}ContractedBox x0 x1 x2 x3 x4 x5) :
    v26Q_R1_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_E3_R1_pilot_Q_eq_assembled]
  exact v26_E3_R1_pilot_assembled_le_gapF x0 x1 x2 x3 x4 x5 hbox

/-- The first exact R1 discard contains no strict counterexample once its R0
contracted box has been established. -/
theorem v26_E3_R1_pilot_no_counterexample
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26E3R0_{wc}ContractedBox x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_E3_R1_pilot_Q_le_gapF x0 x1 x2 x3 x4 x5 hbox
  have hdiscard := v26_discard_R1_{wc} x0 x1 x2 x3 x4 x5
  linarith

end HurtadoZeta23
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    out = Path(ns.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "V26R1DiscardPilotGenerated.lean"
    path.write_text(emit(), encoding="utf-8")
    word, *_ = pilot_data()
    print("R1 ANALYTIC DISCARD PILOT GENERATION OK")
    print("word:", wcode(word))


if __name__ == "__main__":
    main()
