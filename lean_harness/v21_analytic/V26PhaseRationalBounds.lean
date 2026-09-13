import HurtadoZeta23.V26PhaseConstants
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational phase-distortion factor appearing verbatim in the certificate. -/
def v26Mrat (L : ℝ) : ℝ :=
  1 + (193 : ℝ) / (3140 * L ^ 2)

lemma v26_c_div_pi_upper :
    v26c / Real.pi ≤ (193 / 3140 : ℝ) := by
  apply (div_le_iff₀ Real.pi_pos).2
  have hc : v26c ≤ (193 / 1000 : ℝ) := le_of_lt v26_c_upper
  have hpi : (314 / 100 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hrat :
      (193 / 1000 : ℝ) = (193 / 3140 : ℝ) * (314 / 100 : ℝ) := by
    norm_num
  calc
    v26c ≤ (193 / 1000 : ℝ) := hc
    _ = (193 / 3140 : ℝ) * (314 / 100 : ℝ) := hrat
    _ ≤ (193 / 3140 : ℝ) * Real.pi := by
      exact mul_le_mul_of_nonneg_left hpi.le (by norm_num)

/-- The exact phase Lipschitz factor is bounded by the rational one used by
all bootstrap cells. -/
theorem v26_exact_phase_factor_le_rational {L : ℝ} (hL : 0 < L) :
    1 + v26c / (Real.pi * L ^ 2) ≤ v26Mrat L := by
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hratio := v26_c_div_pi_upper
  have hdiv :
      (v26c / Real.pi) / L ^ 2 ≤ (193 / 3140 : ℝ) / L ^ 2 :=
    div_le_div_of_nonneg_right hratio hL2.le
  have hleft :
      v26c / (Real.pi * L ^ 2) = (v26c / Real.pi) / L ^ 2 := by
    field_simp [Real.pi_ne_zero, hL.ne']
  have hright :
      (193 : ℝ) / (3140 * L ^ 2) = (193 / 3140 : ℝ) / L ^ 2 := by
    field_simp [hL.ne']
  unfold v26Mrat
  rw [hleft, hright]
  linarith

lemma v26_Mrat_pos {L : ℝ} (hL : 0 < L) : 0 < v26Mrat L := by
  unfold v26Mrat
  have : 0 ≤ (193 : ℝ) / (3140 * L ^ 2) := by positivity
  linarith

end HurtadoZeta23
