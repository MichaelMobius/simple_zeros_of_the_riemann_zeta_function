#!/usr/bin/env python3
"""Generate kernel-checkable analytic bridges for all 208 R1 discards.

R1 starts from the exact 21-block contracted boxes proved by the 231 R0
survivor modules.  For each of the 208 historical R1 discards this generator
emits:
  * the exact symbolic-root R1 21-block assembly;
  * equality with the historical bootstrap quadratic;
  * analytic domination by the true six-gap functional from the deduplicated
    2,433-cell R1 catalog;
  * exclusion of a strict counterexample via the exact rational R1 discard
    certificate.

Python is not trusted: every emitted analytic/algebraic statement is rechecked
by Lean.  A larger heartbeat budget is installed for generated modules because
some 21-block assemblies are expensive to elaborate.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json

import generate_v26_bootstrap_lean as boot
import generate_v26_r1_cell_catalog as catalog

v = boot.v
CHUNK_SIZE = 10


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


def exact_r1_data():
    words511, _ = v.enumerate_511()
    r0, _d0 = v.run_round(words511, initial=True)
    r1, d1 = v.run_round(r0)
    assert len(r0) == 231 and len(r1) == 23 and len(d1) == 208
    r0_map = {tuple(item[0]): item[1] for item in r0}
    out = []
    for idx, (word, _margin, qmin, nused) in enumerate(d1):
        intervals = r0_map[tuple(word)]
        M, b, c, used = v.build_Q(word, intervals)
        qmin2, _inv, _xstar = v.qmin_and_inverse(M, b, c)
        assert qmin2 == qmin and qmin >= v.delta
        assert len(used) == nused
        out.append((idx, word, intervals, used))
    return out


def emit_word(discard_index: int, word, intervals, used) -> tuple[str, set[int]]:
    wc = wcode(word)
    qtxt, _M, _b, _c, used2 = boot.quadratic_expr(word, intervals)
    assert [(a,b,c,d,e) for a,b,c,d,e,_ in used] == [
        (a,b,c,d,e) for a,b,c,d,e,_ in used2]
    used_by_key = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in used}

    proofs = []
    hnames = []
    bassign = []
    exprs = []
    catalog_modules: set[int] = set()
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

    assembled = f"v26E3R1Assembled_{wc}"
    lower = assembled_lower(exprs)
    hb_names = ", ".join(f"hb{i:02d}" for i in range(21))

    src = f'''/-- Historical R1 block-minorant assembly for discarded word `{wc}`. -/
def {assembled} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {lower}

/-- Pure algebra: the exact historical R1 quadratic for `{wc}` is the symbolic
21-block assembly. -/
theorem v26_E3_R1_Q_eq_assembled_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Q_R1_{wc} x0 x1 x2 x3 x4 x5 =
      {assembled} x0 x1 x2 x3 x4 x5 := by
  unfold v26Q_R1_{wc} {assembled}
  simp [v26Pressure, v21RootRight]
  ring

/-- The R1 assembly for `{wc}` is below the true functional throughout its
exact R0-contracted 21-block box. -/
theorem v26_E3_R1_assembled_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26E3R0_{wc}ContractedBox x0 x1 x2 x3 x4 x5) :
    {assembled} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  unfold v26E3R0_{wc}ContractedBox at hbox
  rcases hbox with ⟨{hb_names}⟩
{chr(10).join(proofs)}
  unfold {assembled}
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(hnames)}

/-- Analytic domination of the exact R1 bootstrap quadratic for `{wc}`. -/
theorem v26_E3_R1_Q_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26E3R0_{wc}ContractedBox x0 x1 x2 x3 x4 x5) :
    v26Q_R1_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_E3_R1_Q_eq_assembled_{wc}]
  exact v26_E3_R1_assembled_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox

/-- R1 discarded word `{wc}` contains no strict counterexample once its exact
R0-contracted input box has been established. -/
theorem v26_E3_R1_no_counterexample_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26E3R0_{wc}ContractedBox x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_E3_R1_Q_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox
  have hdiscard := v26_discard_R1_{wc} x0 x1 x2 x3 x4 x5
  linarith
'''
    return src, catalog_modules


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    items = exact_r1_data()
    modules = []
    for start in range(0, len(items), CHUNK_SIZE):
        chunk_items = items[start:start + CHUNK_SIZE]
        idx = start // CHUNK_SIZE
        name = f"V26R1AnalyticDiscards{idx:02d}Generated"
        bodies = []
        cats: set[int] = set()
        imports = {
            "import HurtadoZeta23.V26GapBlockLower",
            "import Mathlib.Tactic",
        }
        for discard_index, word, intervals, used in chunk_items:
            wc = wcode(word)
            imports.add(f"import HurtadoZeta23.V26BootstrapR1Chunk{discard_index // boot.CHUNK_SIZE}")
            imports.add(f"import HurtadoZeta23.V26R0Survivor{wc}Generated")
            body, cmods = emit_word(discard_index, word, intervals, used)
            bodies.append(body)
            cats |= cmods
        for m in cats:
            imports.add(f"import HurtadoZeta23.V26R1CellCatalog{m:03d}Generated")
        header = "\n".join(sorted(imports)) + '''

set_option maxHeartbeats 1000000

noncomputable section
namespace HurtadoZeta23

'''
        footer = "\nend HurtadoZeta23\n"
        (out_dir / f"{name}.lean").write_text(
            header + "\n".join(bodies) + footer, encoding="utf-8")
        modules.append(name)

    agg = "\n".join(f"import HurtadoZeta23.{m}" for m in modules)
    agg += '''

namespace HurtadoZeta23
/-- Marker: all 208 R1 analytic discard bridges compiled. -/
theorem v26_E3_R1_all_discards_loaded : True := by trivial
end HurtadoZeta23
'''
    agg_path = out_dir / "V26R1AnalyticDiscardsGenerated.lean"
    agg_path.write_text(agg, encoding="utf-8")
    manifest = {
        "discard_count": len(items),
        "chunk_size": CHUNK_SIZE,
        "modules": modules,
        "aggregate_sha256": hashlib.sha256(agg_path.read_bytes()).hexdigest(),
    }
    (out_dir / "v26_r1_analytic_discards_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    manifest = write(Path(ns.out_dir))
    print("R1 ANALYTIC DISCARD GENERATION OK")
    print("discards:", manifest["discard_count"])
    print("modules:", len(manifest["modules"]))


if __name__ == "__main__":
    main()
