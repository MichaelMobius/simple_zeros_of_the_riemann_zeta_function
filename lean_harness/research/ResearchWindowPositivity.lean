import HurtadoZeta23.ResearchWindowActual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

open Real Set MeasureTheory intervalIntegral
open scoped Real Interval

namespace HurtadoZeta23

/-!
# Positivity of the actual pinned nine-point research window

This module is deliberately independent of the upstream arbitrary-window
interface.  The perturbation is tiny compared with the base cosine term, so a
very coarse elementary estimate already gives a strong positive lower bound on
`[-1/2,1/2]`.
-/

/-- Exact sum of the absolute values of the six Fourier perturbation
coefficients. -/
theorem research9_window_perturbation_abs_sum :
    ((3322500 + 7609135 + 1190194 + 731476 + 1680572 + 1141360 : ℕ) : ℝ) /
        1000000000
      = (15675237 / 1000000000 : ℝ) := by
  norm_num

/-- On the half interval, the base cosine is at least `3/4`. -/
theorem research9_window_base_cos_lower_bound
    {s : ℝ} (hs : s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    (3 / 4 : ℝ) ≤ Real.cos (Real.sqrt 2 * s) := by
  have hs_sq : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    exact sq_le_sq' hs.1 hs.2
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have harg_sq : (Real.sqrt 2 * s) ^ 2 ≤ (1 / 2 : ℝ) := by
    calc
      (Real.sqrt 2 * s) ^ 2 = (Real.sqrt 2) ^ 2 * s ^ 2 := by ring
      _ = 2 * s ^ 2 := by rw [hsqrt_sq]
      _ ≤ 2 * (1 / 2 : ℝ) ^ 2 := by nlinarith
      _ = 1 / 2 := by norm_num
  have hcos := Real.one_sub_sq_div_two_le_cos (Real.sqrt 2 * s)
  nlinarith

/-- A strong exact pointwise lower bound for the actual seven-term window. -/
theorem research9_window_lower_bound
    {s : ℝ} (hs : s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    (734324763 / 1000000000 : ℝ) ≤ research9Window s := by
  have hbase := research9_window_base_cos_lower_bound hs
  have h1 := Real.neg_one_le_cos ((2 * Real.pi) * s)
  have h2 := Real.cos_le_one ((4 * Real.pi) * s)
  have h3 := Real.neg_one_le_cos ((6 * Real.pi) * s)
  have h4 := Real.cos_le_one ((8 * Real.pi) * s)
  have h5 := Real.cos_le_one ((10 * Real.pi) * s)
  have h6 := Real.neg_one_le_cos ((12 * Real.pi) * s)
  unfold research9Window
  norm_num at hbase h1 h2 h3 h4 h5 h6 ⊢
  nlinarith

/-- In particular, the actual pinned window is strictly positive throughout
`[-1/2,1/2]`. -/
theorem research9_window_pos
    {s : ℝ} (hs : s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    0 < research9Window s := by
  have h := research9_window_lower_bound hs
  norm_num at h ⊢
  linarith

/-- The actual-window normalizing integral is strictly positive.  This uses
only the already-proved exact normalization identity plus the elementary
location of `1/sqrt 2` inside `(0,pi)`. -/
theorem research9_window_norm_integral_pos :
    0 < research9WindowNormIntegral := by
  rw [research9_window_norm_integral_eq_closed]
  unfold research9v2WindowNorm
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hApos : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr hsqrt_pos
  have hAlt_one : (Real.sqrt 2)⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ hsqrt_gt_one
  have hAlt_pi : (Real.sqrt 2)⁻¹ < Real.pi :=
    lt_trans hAlt_one Real.one_lt_pi
  have hsin : 0 < Real.sin ((Real.sqrt 2)⁻¹) :=
    Real.sin_pos_of_pos_of_lt_pi hApos hAlt_pi
  positivity

end HurtadoZeta23
