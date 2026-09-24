import HurtadoZeta23.ResearchWindowKernelBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

open Real Set MeasureTheory intervalIntegral
open scoped Real Interval

namespace HurtadoZeta23

/-!
# Actual pinned nine-point window

This file connects the exact trigonometric profile used by the pinned
`trmdy/zeta-simple-zeros-673137` certificate to the closed kernel expression
already bounded in `ResearchWindowKernel086v2`.
-/

/-- The exact seven-term trigonometric profile at the pinned upstream commit. -/
def research9Window (s : ℝ) : ℝ :=
  Real.cos (Real.sqrt 2 * s)
    + (3322500 / 1000000000 : ℝ) * Real.cos ((2 * Real.pi) * s)
    - (7609135 / 1000000000 : ℝ) * Real.cos ((4 * Real.pi) * s)
    + (1190194 / 1000000000 : ℝ) * Real.cos ((6 * Real.pi) * s)
    - (731476 / 1000000000 : ℝ) * Real.cos ((8 * Real.pi) * s)
    - (1680572 / 1000000000 : ℝ) * Real.cos ((10 * Real.pi) * s)
    + (1141360 / 1000000000 : ℝ) * Real.cos ((12 * Real.pi) * s)

/-- The interval integral of the actual profile. -/
def research9WindowNormIntegral : ℝ :=
  ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), research9Window s

private lemma research9_sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

private lemma research9_sqrt_two_half :
    Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
    norm_num
  have hn : Real.sqrt 2 ≠ 0 := research9_sqrt_two_ne_zero
  field_simp [hn]
  nlinarith

private lemma research9_integrable_base :
    IntervalIntegrable (fun s : ℝ => Real.cos (Real.sqrt 2 * s))
      volume (-1 / 2) (1 / 2) := by
  exact Continuous.intervalIntegrable (by fun_prop) _ _

private lemma research9_integrable_mode (n : ℕ) (c : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => c * Real.cos ((2 * Real.pi * n) * s))
      volume (-1 / 2) (1 / 2) := by
  exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- All six integer-frequency perturbations have zero mean, so the actual
window normalization is exactly the closed normalization used by the rational
kernel certificate. -/
theorem research9_window_norm_integral_eq_closed :
    research9WindowNormIntegral = research9v2WindowNorm := by
  have h0 := research9_integral_cos (Real.sqrt 2) research9_sqrt_two_ne_zero
  have h1 := research9_integral_integer_cos 1 (by norm_num)
  have h2 := research9_integral_integer_cos 2 (by norm_num)
  have h3 := research9_integral_integer_cos 3 (by norm_num)
  have h4 := research9_integral_integer_cos 4 (by norm_num)
  have h5 := research9_integral_integer_cos 5 (by norm_num)
  have h6 := research9_integral_integer_cos 6 (by norm_num)

  have hi0 := research9_integrable_base
  have hi1 := research9_integrable_mode 1 (3322500 / 1000000000 : ℝ)
  have hi2 := research9_integrable_mode 2 (-(7609135 / 1000000000 : ℝ))
  have hi3 := research9_integrable_mode 3 (1190194 / 1000000000 : ℝ)
  have hi4 := research9_integrable_mode 4 (-(731476 / 1000000000 : ℝ))
  have hi5 := research9_integrable_mode 5 (-(1680572 / 1000000000 : ℝ))
  have hi6 := research9_integrable_mode 6 (1141360 / 1000000000 : ℝ)

  unfold research9WindowNormIntegral research9Window
  rw [intervalIntegral.integral_add hi0
        (hi1.add (hi2.add (hi3.add (hi4.add (hi5.add hi6)))))]
  rw [intervalIntegral.integral_add hi1
        (hi2.add (hi3.add (hi4.add (hi5.add hi6))))]
  rw [intervalIntegral.integral_add hi2
        (hi3.add (hi4.add (hi5.add hi6)))]
  rw [intervalIntegral.integral_add hi3
        (hi4.add (hi5.add hi6))]
  rw [intervalIntegral.integral_add hi4 (hi5.add hi6)]
  rw [intervalIntegral.integral_add hi5 hi6]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [mul_zero, add_zero, sub_zero]
  rw [research9_sqrt_two_half]
  rfl

end HurtadoZeta23
