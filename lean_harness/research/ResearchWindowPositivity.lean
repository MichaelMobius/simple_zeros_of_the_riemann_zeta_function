import HurtadoZeta23.ResearchWindowActual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

open Real Set MeasureTheory intervalIntegral
open scoped Real Interval

namespace HurtadoZeta23

/-!
# Positivity and kernel monotonicity for the actual pinned research window

This module is deliberately independent of the upstream arbitrary-window
interface.  The perturbation is tiny compared with the base cosine term, so a
very coarse elementary estimate already gives a strong positive lower bound on
`[-1/2,1/2]`.  Positivity then gives the needed monotonicity of the normalized
cosine-overlap kernel directly from monotonicity of cosine on `[0,pi]`.
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

/-! ## Monotonicity of the integral-defined kernel -/

/-- Integral numerator for the actual seven-term window at a general frequency
parameter `g`. -/
def research9WindowNumeratorAt (g : ℝ) : ℝ :=
  ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    research9Window s * Real.cos ((2 * Real.pi * g) * s)

/-- Integral-defined normalized kernel for the actual seven-term window. -/
def research9WindowKernelAt (g : ℝ) : ℝ :=
  research9WindowNumeratorAt g / research9WindowNormIntegral

private lemma research9_abs_phase
    {g s : ℝ} (hg : 0 ≤ g) :
    |(2 * Real.pi * g) * s| = 2 * Real.pi * g * |s| := by
  have hcoef : 0 ≤ 2 * Real.pi * g := by
    positivity
  rw [abs_mul, abs_of_nonneg hcoef]

/-- For `s` in the support interval, increasing `g` in `[0,1]` decreases the
cosine factor pointwise. -/
theorem research9_cos_factor_antitone
    {g₁ g₂ s : ℝ}
    (hg₁ : 0 ≤ g₁) (hg₁₂ : g₁ ≤ g₂) (hg₂ : g₂ ≤ 1)
    (hs : s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    Real.cos ((2 * Real.pi * g₂) * s) ≤
      Real.cos ((2 * Real.pi * g₁) * s) := by
  have hg₂nonneg : 0 ≤ g₂ := le_trans hg₁ hg₁₂
  have habss : |s| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hphase₁ := research9_abs_phase (s := s) hg₁
  have hphase₂ := research9_abs_phase (s := s) hg₂nonneg
  have hfac : 0 ≤ 2 * Real.pi * |s| := by
    positivity
  have hphase_le :
      |(2 * Real.pi * g₁) * s| ≤ |(2 * Real.pi * g₂) * s| := by
    rw [hphase₁, hphase₂]
    calc
      2 * Real.pi * g₁ * |s| = g₁ * (2 * Real.pi * |s|) := by ring
      _ ≤ g₂ * (2 * Real.pi * |s|) :=
        mul_le_mul_of_nonneg_right hg₁₂ hfac
      _ = 2 * Real.pi * g₂ * |s| := by ring
  have hgs : g₂ * |s| ≤ (1 : ℝ) * (1 / 2 : ℝ) := by
    calc
      g₂ * |s| ≤ 1 * |s| :=
        mul_le_mul_of_nonneg_right hg₂ (abs_nonneg s)
      _ ≤ 1 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left habss (by norm_num)
  have hphase₂pi : |(2 * Real.pi * g₂) * s| ≤ Real.pi := by
    rw [hphase₂]
    calc
      2 * Real.pi * g₂ * |s| = (2 * Real.pi) * (g₂ * |s|) := by ring
      _ ≤ (2 * Real.pi) * ((1 : ℝ) * (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hgs (by positivity)
      _ = Real.pi := by ring
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg ((2 * Real.pi * g₁) * s)) hphase₂pi hphase_le
  simpa only [Real.cos_abs] using hcos

private lemma research9_window_overlap_integrable (g : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => research9Window s * Real.cos ((2 * Real.pi * g) * s))
      volume (-1 / 2) (1 / 2) := by
  exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The actual-window numerator is antitone on `[0,1]`. -/
theorem research9_window_numerator_antitoneOn :
    AntitoneOn research9WindowNumeratorAt (Set.Icc (0 : ℝ) 1) := by
  intro g₁ hg₁ g₂ hg₂ hg₁₂
  unfold research9WindowNumeratorAt
  exact intervalIntegral.integral_mono_on (by norm_num)
    (research9_window_overlap_integrable g₂)
    (research9_window_overlap_integrable g₁) (by
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (research9_cos_factor_antitone hg₁.1 hg₁₂ hg₂.2 hs)
        (research9_window_pos hs).le)

/-- Because the normalization is positive, the normalized actual-window
kernel is antitone on `[0,1]` as well. -/
theorem research9_window_kernel_antitoneOn :
    AntitoneOn research9WindowKernelAt (Set.Icc (0 : ℝ) 1) := by
  intro g₁ hg₁ g₂ hg₂ hg₁₂
  unfold research9WindowKernelAt
  rw [div_le_div_iff_of_pos_right research9_window_norm_integral_pos]
  exact research9_window_numerator_antitoneOn hg₁ hg₂ hg₁₂

/-- The general integral-defined kernel specializes definitionally to the
already-certified `x = 43/50` kernel. -/
theorem research9_window_kernelAt_086_eq :
    research9WindowKernelAt (43 / 50 : ℝ) = research9WindowKernel086 := by
  rfl

/-- Monotonicity propagates the certified endpoint lower bound to every
`0 <= g <= 43/50`. -/
theorem research9_window_kernel_gt_of_mem_Icc_086
    {g : ℝ} (hg : g ∈ Set.Icc (0 : ℝ) (43 / 50 : ℝ)) :
    (521 / 2500 : ℝ) < research9WindowKernelAt g := by
  have hg_unit : g ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact hg.1
    · nlinarith [hg.2]
  have h086_unit : (43 / 50 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num
  have hmono := research9_window_kernel_antitoneOn hg_unit h086_unit hg.2
  rw [research9_window_kernelAt_086_eq] at hmono
  exact lt_of_lt_of_le research9_window_kernel086_gt hmono

end HurtadoZeta23
