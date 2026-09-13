import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Moving a root by less than `10^-5` to its rational endpoint costs only the
published `999 * 10^-10` additive error. -/
theorem v26_rational_center_lower {x r q : ℝ}
    (hrq : |r - q| < (1 / 100000 : ℝ)) :
    (999 / 1000 : ℝ) * (x - q) ^ 2 - (999 / 10000000000 : ℝ)
      ≤ (x - r) ^ 2 := by
  have hv2 : (r - q) ^ 2 < (1 / 100000 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    simpa using hrq
  have hs : 0 ≤ ((x - q) - 1000 * (r - q)) ^ 2 := sq_nonneg _
  have hbase :
      (999 / 1000 : ℝ) * (x - q) ^ 2 - 999 * (r - q) ^ 2
        ≤ (x - r) ^ 2 := by
    nlinarith
  have herr :
      (999 / 1000 : ℝ) * (x - q) ^ 2 - (999 / 10000000000 : ℝ)
        ≤ (999 / 1000 : ℝ) * (x - q) ^ 2 - 999 * (r - q) ^ 2 := by
    norm_num at hv2 ⊢
    nlinarith
  exact herr.trans hbase

/-- Generic weakening step used after the analytic root-centred minorant.
`alpha` may be rounded down and `eta` rounded up; the resulting rational
quadratic remains a valid lower bound. -/
theorem v26_rounded_minorant_of_root_minorant
    {weight A alpha eta x r q : ℝ}
    (hA : 0 ≤ A)
    (hroot : A * (x - r) ^ 2 ≤ weight)
    (hrq : |r - q| < (1 / 100000 : ℝ))
    (halpha : alpha ≤ (999 / 1000 : ℝ) * A)
    (heta : (999 / 10000000000 : ℝ) * A ≤ eta) :
    alpha * (x - q) ^ 2 - eta ≤ weight := by
  have hc := mul_le_mul_of_nonneg_left (v26_rational_center_lower (x := x) hrq) hA
  have hs : 0 ≤ (x - q) ^ 2 := sq_nonneg _
  have ha := mul_le_mul_of_nonneg_right halpha hs
  nlinarith

end HurtadoZeta23
