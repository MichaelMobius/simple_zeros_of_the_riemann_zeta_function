import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

lemma v26_sin_abs_sq (y : ℝ) :
    Real.sin |y| ^ 2 = Real.sin y ^ 2 := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_nonpos hy, Real.sin_neg]
    ring

/-- Squaring removes both the integer phase sign and the sign of the phase
displacement. -/
theorem v26_sin_phase_sq_distance (N : ℕ) (z : ℝ) :
    Real.sin (Real.pi * z) ^ 2 =
      Real.sin (Real.pi * |z - (N : ℝ)|) ^ 2 := by
  let d : ℝ := z - (N : ℝ)
  have harg : Real.pi * z = Real.pi * d + (N : ℝ) * Real.pi := by
    dsimp [d]
    ring
  rw [harg, Real.sin_add_nat_mul_pi]
  have hsgn : ((-1 : ℝ) ^ N) ^ 2 = 1 := by
    rw [← sq_abs, abs_neg_one_pow]
    norm_num
  rw [mul_pow, hsgn, one_mul]
  have habs := (v26_sin_abs_sq (Real.pi * d)).symm
  have hpiabs : |Real.pi * d| = Real.pi * |d| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hpiabs] at habs
  simpa [d] using habs

end HurtadoZeta23
