#!/usr/bin/env python3
"""Generate analytic Q<=F bridges for all 280 discarded R0 words.

This is Package E3's first full transport/discard layer. It reuses:
  * the exact rational discard theorems from generate_v26_bootstrap_lean.py;
  * the 190 deduplicated analytic cell theorems from the R0 cell catalog;
  * the generic 21-block positive-weight assembly lemma.

For every discarded word, Lean proves from its actual Package-D A-B-C-C-B-A
box that the historical rounded quadratic is below v26GapF limitingWeight and
therefore cannot contain a strict counterexample. Python only serializes exact
Fraction data; all implications are kernel checked.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import argparse
import importlib.util
import hashlib
import json

import generate_v26_r0_cell_catalog as catalog

HERE = Path(__file__).resolve().parent
VERIFIER = HERE / "v21_rational_bootstrap_verify.py"
CHUNK_SIZE = 10


def load_verifier():
    spec = importlib.util.spec_from_file_location("v26_r0_analytic_discards", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load exact verifier")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


v = load_verifier()


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


def lower_proof(i: int, r: int) -> str:
    hs = ", ".join(f"h{j}.1" for j in range(i, i + r))
    return f"(by linarith [{hs}])"


def upper_proof(i: int, r: int) -> str:
    hs = ", ".join(f"h{j}.2" for j in range(i, i + r))
    return f"(by linarith [{hs}])"


def word_value(w) -> str:
    tys = [7, 5, 6, 6, 5, 7]
    vals = [d - 1 for d in w]
    return "(" + ", ".join(f"({a} : Fin {n})" for a, n in zip(vals, tys)) + ")"


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


def emit_word(w, intervals) -> str:
    wc = wcode(w)
    _M, _b, _c, used = v.build_Q(w, intervals)
    used_by_key = {(i, r): (N, alpha, eta) for i, r, N, alpha, eta, _rho in used}

    proofs = []
    hnames = []
    bassign = []
    exprs = []
    used_count = 0
    for r in range(1, 7):
        for i in range(7 - r):
            s = bsum(i, r)
            if (i, r) in used_by_key:
                N, alpha, eta = used_by_key[(i, r)]
                L, U = intervals[(i, r)]
                key = catalog.cell_key(L, U, N, alpha, eta)
                idx = catalog.CELL_INDEX[key]
                hn = f"hm{used_count}"
                expr = minor_expr(N, alpha, eta, s)
                proofs.append(
                    f"  have {hn} := v26_R0_cell_{idx:03d} (x := {s})\n"
                    f"    {lower_proof(i, r)} {upper_proof(i, r)}"
                )
                used_count += 1
            else:
                hn = f"hn_{i}_{r}"
                expr = "0"
                proofs.append(f"  have {hn} := v26_limitingWeight_nonneg ({s})")
            hnames.append(hn)
            bassign.append(f"    ({block_name(r, i)} := {expr})")
            exprs.append(expr)

    assert used_count == len(used)
    assert len(exprs) == 21
    lower = assembled_lower(exprs)
    word_def = f"v26E3R0Word_{wc}"
    assembled = f"v26E3R0Assembled_{wc}"

    return f'''/-- Concrete basin word for R0 code `{wc}`. -/
def {word_def} : V26BasinWord := {word_value(w)}

/-- Historical R0 block-minorant assembly for `{wc}`. -/
def {assembled} (x0 x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  {lower}

/-- Pure algebra: the generated rational bootstrap quadratic for `{wc}` is
exactly its 21-block assembled lower form. -/
theorem v26_E3_R0_Q_eq_assembled_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ) :
    v26Q_R0_{wc} x0 x1 x2 x3 x4 x5 =
      {assembled} x0 x1 x2 x3 x4 x5 := by
  unfold v26Q_R0_{wc} {assembled}
  simp [v26Pressure, v21RootRight, Matrix.cons_val_succ']
  ring

/-- The assembled R0 minorant for `{wc}` is below the actual six-gap
functional throughout its exact Package-D basin box. -/
theorem v26_E3_R0_assembled_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5) :
    {assembled} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  simp [v26InWordBox, {word_def},
    v26InA, v26InB, v26InC,
    v26ALo, v26AHi, v26BLo, v26BHi, v26CLo, v26CHi] at hbox
  norm_num at hbox
  rcases hbox with ⟨h0, h1, h2, h3, h4, h5⟩
{chr(10).join(proofs)}
  unfold {assembled}
  exact v26_gapF_lower_of_block_lowers
    (weight := limitingWeight)
    (g0 := x0) (g1 := x1) (g2 := x2) (g3 := x3) (g4 := x4) (g5 := x5)
{chr(10).join(bassign)}
    {' '.join(hnames)}

/-- Analytic domination of the exact R0 bootstrap quadratic for `{wc}`. -/
theorem v26_E3_R0_Q_le_gapF_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5) :
    v26Q_R0_{wc} x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  rw [v26_E3_R0_Q_eq_assembled_{wc}]
  exact v26_E3_R0_assembled_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox

/-- The discarded R0 word `{wc}` contains no strict counterexample. -/
theorem v26_E3_R0_no_counterexample_{wc}
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox {word_def} x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_E3_R0_Q_le_gapF_{wc} x0 x1 x2 x3 x4 x5 hbox
  have hdiscard := v26_discard_R0_{wc} x0 x1 x2 x3 x4 x5
  linarith
'''


def exact_r0_discards():
    words511, _ = v.enumerate_511()
    _survivors, discards = v.run_round(words511, initial=True)
    assert len(discards) == 280
    return [(w, v.initial_intervals(w)) for w, _margin, _qmin, _nused in discards]


def write(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    items = exact_r0_discards()
    modules = []
    header = '''import HurtadoZeta23.V26BootstrapDiscardGenerated
import HurtadoZeta23.V26R0CellCatalogGenerated
import HurtadoZeta23.V26GapBlockLower
import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

'''
    footer = '\nend HurtadoZeta23\n'
    for start in range(0, len(items), CHUNK_SIZE):
        idx = start // CHUNK_SIZE
        name = f"V26R0AnalyticDiscards{idx:02d}Generated"
        body = "\n".join(emit_word(w, intervals) for w, intervals in items[start:start + CHUNK_SIZE])
        (out_dir / f"{name}.lean").write_text(header + body + footer, encoding="utf-8")
        modules.append(name)

    agg = "\n".join(f"import HurtadoZeta23.{name}" for name in modules)
    agg += '''

namespace HurtadoZeta23
/-- Marker: all 280 R0 analytic discard bridges compiled. -/
theorem v26_E3_R0_all_discards_loaded : True := by trivial
end HurtadoZeta23
'''
    agg_path = out_dir / "V26R0AnalyticDiscardsGenerated.lean"
    agg_path.write_text(agg, encoding="utf-8")

    manifest = {
        "discard_count": len(items),
        "chunk_size": CHUNK_SIZE,
        "modules": modules,
        "aggregate_sha256": hashlib.sha256(agg_path.read_bytes()).hexdigest(),
    }
    (out_dir / "v26_r0_analytic_discards_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return manifest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ns = ap.parse_args()
    manifest = write(Path(ns.out_dir))
    print("R0 ANALYTIC DISCARD GENERATION OK")
    print("discards:", manifest["discard_count"])
    print("modules:", len(manifest["modules"]))


if __name__ == "__main__":
    main()
