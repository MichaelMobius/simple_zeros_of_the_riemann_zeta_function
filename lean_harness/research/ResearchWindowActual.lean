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

  unfold research9WindowNormIntegral
  have hshape :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), research9Window s) =
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (Real.sqrt 2 * s) +
        ((3322500 / 1000000000 : ℝ) * Real.cos ((2 * Real.pi * (1 : ℝ)) * s) +
        (-(7609135 / 1000000000 : ℝ)) * Real.cos ((2 * Real.pi * (2 : ℝ)) * s) +
        ((1190194 / 1000000000 : ℝ) * Real.cos ((2 * Real.pi * (3 : ℝ)) * s) +
        (-(731476 / 1000000000 : ℝ)) * Real.cos ((2 * Real.pi * (4 : ℝ)) * s) +
        ((-(1680572 / 1000000000 : ℝ)) * Real.cos ((2 * Real.pi * (5 : ℝ)) * s) +
        (1141360 / 1000000000 : ℝ) * Real.cos ((2 * Real.pi * (6 : ℝ)) * s))) := by
    apply intervalIntegral.integral_congr
    intro s _
    unfold research9Window
    ring_nf
  rw [hshape]
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
  norm_num at h1 h2 h3 h4 h5 h6
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [mul_zero, add_zero]
  rw [research9_sqrt_two_half]
  unfold research9v2WindowNorm
  rfl

/-! ## Actual-window numerator at x = 43/50 -/

private def research9ActualA : ℝ := (Real.sqrt 2)⁻¹
private def research9ActualTheta : ℝ := (7 / 50 : ℝ) * Real.pi
private def research9ActualB : ℝ := (43 / 50 : ℝ) * Real.pi
private def research9ActualX : ℝ := 43 / 50

private def research9ActualBase : ℝ :=
  (research9ActualA * Real.sin research9ActualA * Real.cos research9ActualTheta +
      research9ActualB * Real.cos research9ActualA * Real.sin research9ActualTheta) /
    (research9ActualB ^ 2 - research9ActualA ^ 2)

private def research9ActualPiece (n : ℕ) : ℝ :=
  research9ActualX * Real.sin research9ActualTheta /
    (Real.pi * (((n : ℝ) ^ 2) - research9ActualX ^ 2))

/-- A public mirror of the exact closed raw expression used by
`ResearchWindowKernel086v2`.  The next theorem checks that the mirror is
literally the same real number as the certified expression. -/
def research9WindowRawClosed086 : ℝ :=
  research9ActualBase
  + (3322500 / 1000000000 : ℝ) * research9ActualPiece 1
  + (7609135 / 1000000000 : ℝ) * research9ActualPiece 2
  + (1190194 / 1000000000 : ℝ) * research9ActualPiece 3
  + (731476 / 1000000000 : ℝ) * research9ActualPiece 4
  - (1680572 / 1000000000 : ℝ) * research9ActualPiece 5
  - (1141360 / 1000000000 : ℝ) * research9ActualPiece 6

/-- The public mirror is definitionally identical to the closed raw quantity
already certified in `ResearchWindowKernel086v2`. -/
theorem research9_window_raw_closed086_eq_v2 :
    research9WindowRawClosed086 = research9v2WindowRaw086 := by
  rfl

private lemma research9_actual_A_pos : 0 < research9ActualA := by
  unfold research9ActualA
  positivity

private lemma research9_actual_A_sq : research9ActualA ^ 2 = (1 / 2 : ℝ) := by
  unfold research9ActualA
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma research9_actual_B_gt_A : research9ActualA < research9ActualB := by
  have hA_lt_one : research9ActualA < 1 := by
    nlinarith [research9_actual_A_sq, research9_actual_A_pos]
  unfold research9ActualB
  nlinarith [Real.pi_gt_three]

private lemma research9_actual_base_overlap_eq_closed :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (Real.sqrt 2 * s) *
          Real.cos ((2 * Real.pi * research9ActualX) * s))
      = research9ActualBase := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt_lt_two : Real.sqrt 2 < 2 := by
    nlinarith
  have hfreq : Real.sqrt 2 < 2 * Real.pi * research9ActualX := by
    unfold research9ActualX
    nlinarith [Real.pi_gt_three]
  have h := research9_integral_cos_mul_cos
    (Real.sqrt 2) (2 * Real.pi * research9ActualX)
    (by nlinarith) (by positivity)
  have harg1 :
      (Real.sqrt 2 - 2 * Real.pi * research9ActualX) / 2 =
        research9ActualA - research9ActualB := by
    unfold research9ActualA research9ActualB research9ActualX
    rw [research9_sqrt_two_half]
    ring
  have harg2 :
      (Real.sqrt 2 + 2 * Real.pi * research9ActualX) / 2 =
        research9ActualA + research9ActualB := by
    unfold research9ActualA research9ActualB research9ActualX
    rw [research9_sqrt_two_half]
    ring
  have hden1 :
      Real.sqrt 2 - 2 * Real.pi * research9ActualX =
        2 * (research9ActualA - research9ActualB) := by
    unfold research9ActualA research9ActualB research9ActualX
    have hs : Real.sqrt 2 = 2 * (Real.sqrt 2)⁻¹ := by
      nlinarith [research9_sqrt_two_half]
    rw [hs]
    ring
  have hden2 :
      Real.sqrt 2 + 2 * Real.pi * research9ActualX =
        2 * (research9ActualA + research9ActualB) := by
    unfold research9ActualA research9ActualB research9ActualX
    have hs : Real.sqrt 2 = 2 * (Real.sqrt 2)⁻¹ := by
      nlinarith [research9_sqrt_two_half]
    rw [hs]
    ring
  rw [harg1, harg2, hden1, hden2] at h
  have hBtheta : research9ActualB = Real.pi - research9ActualTheta := by
    unfold research9ActualB research9ActualTheta
    ring
  have hsin1 :
      Real.sin (research9ActualA - research9ActualB) =
        -(Real.sin research9ActualA * Real.cos research9ActualTheta +
          Real.cos research9ActualA * Real.sin research9ActualTheta) := by
    rw [hBtheta]
    rw [show research9ActualA - (Real.pi - research9ActualTheta) =
        (research9ActualA + research9ActualTheta) - Real.pi by ring]
    rw [Real.sin_sub_pi, Real.sin_add]
    ring
  have hsin2 :
      Real.sin (research9ActualA + research9ActualB) =
        -(Real.sin research9ActualA * Real.cos research9ActualTheta -
          Real.cos research9ActualA * Real.sin research9ActualTheta) := by
    rw [hBtheta]
    rw [show research9ActualA + (Real.pi - research9ActualTheta) =
        (research9ActualA - research9ActualTheta) + Real.pi by ring]
    rw [Real.sin_add_pi, Real.sin_sub]
    ring
  have hminus : research9ActualA - research9ActualB ≠ 0 := by
    nlinarith [research9_actual_B_gt_A]
  have hplus : research9ActualA + research9ActualB ≠ 0 := by
    have hBpos : 0 < research9ActualB := by
      unfold research9ActualB
      positivity
    nlinarith [research9_actual_A_pos]
  have hsqpos : 0 < research9ActualB ^ 2 - research9ActualA ^ 2 := by
    have hprod :
        0 < (research9ActualB - research9ActualA) *
          (research9ActualB + research9ActualA) := by
      apply mul_pos
      · exact sub_pos.mpr research9_actual_B_gt_A
      · nlinarith [research9_actual_A_pos, research9_actual_B_gt_A]
    nlinarith
  calc
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (Real.sqrt 2 * s) *
          Real.cos ((2 * Real.pi * research9ActualX) * s))
        = Real.sin (research9ActualA - research9ActualB) /
              (2 * (research9ActualA - research9ActualB))
          + Real.sin (research9ActualA + research9ActualB) /
              (2 * (research9ActualA + research9ActualB)) := h
    _ = research9ActualBase := by
      rw [hsin1, hsin2]
      unfold research9ActualBase
      field_simp [hminus, hplus, ne_of_gt hsqpos]
      ring

private lemma research9_actual_mode_overlap_succ (k : ℕ) :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos ((2 * Real.pi * ((k : ℝ) + 1)) * s) *
          Real.cos ((2 * Real.pi * research9ActualX) * s))
      = (-1 : ℝ) ^ k * research9ActualPiece (k + 1) := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hminuspos : 0 < (k : ℝ) + 1 - research9ActualX := by
    unfold research9ActualX
    nlinarith
  have hpluspos : 0 < (k : ℝ) + 1 + research9ActualX := by
    unfold research9ActualX
    nlinarith
  have hsub :
      2 * Real.pi * ((k : ℝ) + 1) - 2 * Real.pi * research9ActualX ≠ 0 := by
    have hp : 0 < (2 * Real.pi) * ((k : ℝ) + 1 - research9ActualX) := by
      exact mul_pos (by positivity) hminuspos
    convert ne_of_gt hp using 1 <;> ring
  have hadd :
      2 * Real.pi * ((k : ℝ) + 1) + 2 * Real.pi * research9ActualX ≠ 0 := by
    have hp : 0 < (2 * Real.pi) * ((k : ℝ) + 1 + research9ActualX) := by
      exact mul_pos (by positivity) hpluspos
    convert ne_of_gt hp using 1 <;> ring
  have h := research9_integral_cos_mul_cos
    (2 * Real.pi * ((k : ℝ) + 1))
    (2 * Real.pi * research9ActualX) hsub hadd
  have harg1 :
      (2 * Real.pi * ((k : ℝ) + 1) - 2 * Real.pi * research9ActualX) / 2 =
        research9ActualTheta + (k : ℝ) * Real.pi := by
    unfold research9ActualTheta research9ActualX
    ring
  have harg2 :
      (2 * Real.pi * ((k : ℝ) + 1) + 2 * Real.pi * research9ActualX) / 2 =
        ((k + 2 : ℕ) : ℝ) * Real.pi - research9ActualTheta := by
    unfold research9ActualTheta research9ActualX
    push_cast
    ring
  have hden1 :
      2 * Real.pi * ((k : ℝ) + 1) - 2 * Real.pi * research9ActualX =
        2 * Real.pi * ((k : ℝ) + 1 - research9ActualX) := by ring
  have hden2 :
      2 * Real.pi * ((k : ℝ) + 1) + 2 * Real.pi * research9ActualX =
        2 * Real.pi * ((k : ℝ) + 1 + research9ActualX) := by ring
  rw [harg1, harg2, hden1, hden2] at h
  rw [Real.sin_add_nat_mul_pi, Real.sin_nat_mul_pi_sub] at h
  have hpow : (-1 : ℝ) ^ (k + 2) = (-1 : ℝ) ^ k := by
    rw [pow_add]
    norm_num
  rw [hpow] at h
  have hminus : (k : ℝ) + 1 - research9ActualX ≠ 0 := ne_of_gt hminuspos
  have hplus : (k : ℝ) + 1 + research9ActualX ≠ 0 := ne_of_gt hpluspos
  have hsqpos :
      0 < ((k : ℝ) + 1) ^ 2 - research9ActualX ^ 2 := by
    have hprod :
        0 < (((k : ℝ) + 1) - research9ActualX) *
          (((k : ℝ) + 1) + research9ActualX) :=
      mul_pos hminuspos hpluspos
    nlinarith
  calc
    (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos ((2 * Real.pi * ((k : ℝ) + 1)) * s) *
          Real.cos ((2 * Real.pi * research9ActualX) * s))
        = (-1 : ℝ) ^ k * Real.sin research9ActualTheta /
              (2 * Real.pi * ((k : ℝ) + 1 - research9ActualX))
          - (-1 : ℝ) ^ k * Real.sin research9ActualTheta /
              (2 * Real.pi * ((k : ℝ) + 1 + research9ActualX)) := by
            simpa only [neg_mul, neg_div] using h
    _ = (-1 : ℝ) ^ k * research9ActualPiece (k + 1) := by
      unfold research9ActualPiece
      push_cast
      field_simp [Real.pi_ne_zero, hminus, hplus, ne_of_gt hsqpos]
      ring

private lemma research9_integrable_overlap (a c : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => c *
        (Real.cos (a * s) *
          Real.cos ((2 * Real.pi * research9ActualX) * s)))
      volume (-1 / 2) (1 / 2) := by
  exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The actual-window numerator at `x = 43/50`. -/
def research9WindowNumerator086 : ℝ :=
  ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    research9Window s * Real.cos ((2 * Real.pi * research9ActualX) * s)

/-- The seven cosine overlaps reproduce the exact raw closed expression used
by the rational/transcendental certificate. -/
theorem research9_window_numerator086_eq_closed :
    research9WindowNumerator086 = research9WindowRawClosed086 := by
  have h0 := research9_actual_base_overlap_eq_closed
  have h1 :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Real.cos ((2 * Real.pi * (1 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s))
        = research9ActualPiece 1 := by
    simpa using (research9_actual_mode_overlap_succ 0)
  have h2 :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Real.cos ((2 * Real.pi * (2 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s))
        = -research9ActualPiece 2 := by
    simpa using (research9_actual_mode_overlap_succ 1)
  have h3 :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Real.cos ((2 * Real.pi * (3 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s))
        = research9ActualPiece 3 := by
    simpa using (research9_actual_mode_overlap_succ 2)
  have h4 :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Real.cos ((2 * Real.pi * (4 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s))
        = -research9ActualPiece 4 := by
    simpa using (research9_actual_mode_overlap_succ 3)
  have h5 :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Real.cos ((2 * Real.pi * (5 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s))
        = research9ActualPiece 5 := by
    simpa using (research9_actual_mode_overlap_succ 4)
  have h6 :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Real.cos ((2 * Real.pi * (6 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s))
        = -research9ActualPiece 6 := by
    simpa using (research9_actual_mode_overlap_succ 5)

  have hi0 := research9_integrable_overlap (Real.sqrt 2) 1
  have hi1 := research9_integrable_overlap (2 * Real.pi * (1 : ℝ))
    (3322500 / 1000000000 : ℝ)
  have hi2 := research9_integrable_overlap (2 * Real.pi * (2 : ℝ))
    (-(7609135 / 1000000000 : ℝ))
  have hi3 := research9_integrable_overlap (2 * Real.pi * (3 : ℝ))
    (1190194 / 1000000000 : ℝ)
  have hi4 := research9_integrable_overlap (2 * Real.pi * (4 : ℝ))
    (-(731476 / 1000000000 : ℝ))
  have hi5 := research9_integrable_overlap (2 * Real.pi * (5 : ℝ))
    (-(1680572 / 1000000000 : ℝ))
  have hi6 := research9_integrable_overlap (2 * Real.pi * (6 : ℝ))
    (1141360 / 1000000000 : ℝ)

  unfold research9WindowNumerator086
  have hshape :
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          research9Window s * Real.cos ((2 * Real.pi * research9ActualX) * s)) =
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        (1 : ℝ) * (Real.cos (Real.sqrt 2 * s) *
          Real.cos ((2 * Real.pi * research9ActualX) * s)) +
        ((3322500 / 1000000000 : ℝ) *
          (Real.cos ((2 * Real.pi * (1 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s)) +
        (-(7609135 / 1000000000 : ℝ)) *
          (Real.cos ((2 * Real.pi * (2 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s)) +
        ((1190194 / 1000000000 : ℝ) *
          (Real.cos ((2 * Real.pi * (3 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s)) +
        (-(731476 / 1000000000 : ℝ)) *
          (Real.cos ((2 * Real.pi * (4 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s)) +
        ((-(1680572 / 1000000000 : ℝ)) *
          (Real.cos ((2 * Real.pi * (5 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s)) +
        (1141360 / 1000000000 : ℝ) *
          (Real.cos ((2 * Real.pi * (6 : ℝ)) * s) *
            Real.cos ((2 * Real.pi * research9ActualX) * s)))) := by
    apply intervalIntegral.integral_congr
    intro s _
    unfold research9Window
    ring_nf
  rw [hshape]
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
  unfold research9WindowRawClosed086
  ring

/-- The actual-window numerator is exactly the certified raw quantity. -/
theorem research9_window_numerator086_eq_v2 :
    research9WindowNumerator086 = research9v2WindowRaw086 := by
  rw [research9_window_numerator086_eq_closed, research9_window_raw_closed086_eq_v2]

/-- Integral-defined normalized kernel of the actual seven-term window at
`x = 43/50`. -/
def research9WindowKernel086 : ℝ :=
  research9WindowNumerator086 / research9WindowNormIntegral

/-- The integral-defined actual-window kernel is exactly the closed kernel
certified in `ResearchWindowKernel086v2`. -/
theorem research9_window_kernel086_eq_closed :
    research9WindowKernel086 = research9v2WindowKernelClosed086 := by
  unfold research9WindowKernel086 research9v2WindowKernelClosed086
  rw [research9_window_numerator086_eq_v2, research9_window_norm_integral_eq_closed]

/-- Final actual-window kernel inequality needed by the hybrid block argument. -/
theorem research9_window_kernel086_gt :
    (521 / 2500 : ℝ) < research9WindowKernel086 := by
  rw [research9_window_kernel086_eq_closed]
  exact research9v2_window_kernel_closed_gt

/-- Literal integral-ratio form of the target inequality. -/
theorem research9_window_integral_ratio086_gt :
    (521 / 2500 : ℝ) <
      (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          research9Window s * Real.cos ((2 * Real.pi * (43 / 50 : ℝ)) * s)) /
        (∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), research9Window s) := by
  simpa [research9WindowKernel086, research9WindowNumerator086,
    research9WindowNormIntegral, research9ActualX] using research9_window_kernel086_gt

end HurtadoZeta23
