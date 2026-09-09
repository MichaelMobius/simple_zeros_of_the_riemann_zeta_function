import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational bounds that will be consumed by the analytic kernel proof. -/
theorem v20_pi_lower_target : (31415926 / 10000000 : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  norm_num at h ⊢
  linarith

/-- A deliberately coarse upper bound; it is enough for the final certificate. -/
theorem v20_pi_upper_coarse : Real.pi < (22 / 7 : ℝ) := by
  exact Real.pi_lt_22_div_7

end HurtadoZeta23
