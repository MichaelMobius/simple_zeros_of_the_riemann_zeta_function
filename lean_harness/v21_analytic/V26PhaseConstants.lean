import HurtadoZeta23.V21KernelCellTools
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Coefficient in the article's rational phase form of the limiting kernel. -/
def v26C0 : ℝ := v21C / Real.pi

/-- Phase-shift coefficient in the article's rational phase form.  Using
`v21C = cos(a)/(sqrt 2 sin(a))`, this equals `a tan(a) / pi`. -/
def v26c : ℝ := 1 / (2 * v21C * Real.pi)

/-- Exact denominator constant in the normalized kernel. -/
def v26dk : ℝ := 1 / (2 * Real.pi ^ 2)

/-- Rational denominator constant used in all bootstrap minorants. -/
def v26d0 : ℝ := 1 / (2 * (3142 / 1000 : ℝ) ^ 2)

lemma v26_C_pos : 0 < v21C := v21_C_gt_half.trans' (by norm_num)

lemma v26_C0_pos : 0 < v26C0 := by
  unfold v26C0
  exact div_pos v26_C_pos Real.pi_pos

lemma v26_c_pos : 0 < v26c := by
  unfold v26c
  have h2C : 0 < 2 * v21C := mul_pos (by norm_num) v26_C_pos
  have hden : 0 < 2 * v21C * Real.pi := mul_pos h2C Real.pi_pos
  exact one_div_pos.mpr hden

/-- Directed rational lower bound used in every phase minorant. -/
theorem v26_C0_lower :
    (2633 / 10000 : ℝ) < v26C0 := by
  unfold v26C0
  apply (lt_div_iff₀ Real.pi_pos).2
  calc
    (2633 / 10000 : ℝ) * Real.pi
        < (2633 / 10000 : ℝ) * (31415927 / 10000000 : ℝ) := by
          exact mul_lt_mul_of_pos_left v21_pi_upper (by norm_num)
    _ < (88280819 / 106683860 : ℝ) := by norm_num
    _ ≤ v21C := v21_C_lower

/-- Directed rational upper bound for the phase shift. -/
theorem v26_c_upper :
    v26c < (193 / 1000 : ℝ) := by
  have h2C : 0 < 2 * v21C := mul_pos (by norm_num) v26_C_pos
  have hden : 0 < 2 * v21C * Real.pi := mul_pos h2C Real.pi_pos
  unfold v26c
  apply (div_lt_iff₀ hden).2
  have hprod :
      (88280819 / 106683860 : ℝ) * (31415926 / 10000000 : ℝ)
        < v21C * Real.pi := by
    calc
      (88280819 / 106683860 : ℝ) * (31415926 / 10000000 : ℝ)
          < (88280819 / 106683860 : ℝ) * Real.pi := by
            exact mul_lt_mul_of_pos_left v21_pi_lower (by norm_num)
      _ ≤ v21C * Real.pi := by
            exact mul_le_mul_of_nonneg_right v21_C_lower Real.pi_pos.le
  have hscaled :
      (193 / 1000 : ℝ) *
          (2 * (88280819 / 106683860 : ℝ) * (31415926 / 10000000 : ℝ))
        < (193 / 1000 : ℝ) * (2 * v21C * Real.pi) := by
    apply mul_lt_mul_of_pos_left
    · nlinarith
    · norm_num
  have hrat :
      (1 : ℝ) <
        (193 / 1000 : ℝ) *
          (2 * (88280819 / 106683860 : ℝ) * (31415926 / 10000000 : ℝ)) := by
    norm_num
  exact hrat.trans hscaled

lemma v26_pi_lt_3142 : Real.pi < (3142 / 1000 : ℝ) := by
  exact v21_pi_upper.trans (by norm_num)

/-- The rational denominator weakening really lies below the exact one. -/
theorem v26_d0_lt_dk : v26d0 < v26dk := by
  unfold v26d0 v26dk
  have hp2 : 0 < 2 * Real.pi ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  have hden :
      2 * Real.pi ^ 2 < 2 * (3142 / 1000 : ℝ) ^ 2 := by
    have hp := v26_pi_lt_3142
    have hp0 : 0 < (3142 / 1000 : ℝ) := by norm_num
    nlinarith [Real.pi_pos, sq_nonneg ((3142 / 1000 : ℝ) - Real.pi)]
  exact one_div_lt_one_div_of_lt hp2 hden

end HurtadoZeta23
