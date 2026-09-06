import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# v17 strong-block scalar contradiction core

This file isolates the exact rational algebra in the `m = 450` block argument.
It deliberately assumes the three analytic/spectral inputs separately:

* `A ≤ E + P` from seven-point redistribution,
* `t*g0*Q ≤ D + t*P` from adjacent-pair energy plus the scalar kernel bound,
* `D < E → 450/449 < D` from the spectral-threshold lemma.

No zeta-function or matrix theory occurs here.
-/

def v17A : ℝ := 4329 / 2500

def v17Q : ℝ := 111 / 125

def v17g0 : ℝ := 4449 / 5000

def v17t : ℝ := 33 / 2

def v17Threshold : ℝ := 450 / 449

/-- Exact positive contradiction margin for the Q60-compatible witness
`g0 = 4449/5000`, `t = 33/2`. -/
theorem v17_contradiction_margin :
    0 < v17g0 * v17Q + (1 - 1 / v17t) * v17Threshold - v17A := by
  norm_num [v17g0, v17Q, v17t, v17Threshold, v17A]

/-- The exact rational value of the contradiction margin. -/
theorem v17_contradiction_margin_exact :
    v17g0 * v17Q + (1 - 1 / v17t) * v17Threshold - v17A
      = 88071 / 3086875000 := by
  norm_num [v17g0, v17Q, v17t, v17Threshold, v17A]

/-- Scalar finishing lemma for the strong `m=450` block estimate. -/
theorem v17_strong_block_scalar
    {D E P : ℝ}
    (hEP : v17A ≤ E + P)
    (hweighted : v17t * v17g0 * v17Q ≤ D + v17t * P)
    (hthreshold : D < E → v17Threshold < D) :
    v17A ≤ D + P := by
  by_contra hnot
  have hDP : D + P < v17A := lt_of_not_ge hnot
  have hDE : D < E := by
    linarith
  have hD : v17Threshold < D := hthreshold hDE
  have hupper :
      D + v17t * P <
        v17t * v17A - (v17t - 1) * v17Threshold := by
    have hid : D + v17t * P = v17t * (D + P) - (v17t - 1) * D := by
      ring
    rw [hid]
    have htpos : 0 < v17t := by norm_num [v17t]
    have htm1pos : 0 < v17t - 1 := by norm_num [v17t]
    nlinarith
  have hmargin :
      v17t * v17A - (v17t - 1) * v17Threshold
        < v17t * v17g0 * v17Q := by
    have hm := v17_contradiction_margin
    have htpos : 0 < v17t := by norm_num [v17t]
    field_simp [ne_of_gt htpos] at hm ⊢
    nlinarith
  linarith

end HurtadoZeta23
