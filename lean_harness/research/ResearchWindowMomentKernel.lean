import HurtadoZeta23.ResearchWindowKernelBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

open Real Set MeasureTheory intervalIntegral
open scoped Real Interval

namespace HurtadoZeta23

/-!
# Absolute-distance cosine kernel on the unit core

This is the reusable moment identity needed to turn the double integral in
`ThmD.cFun` into ordinary cosine overlaps.  It is deliberately independent of
the six pinned perturbation coefficients.
-/

private theorem research9_hasDerivAt_kernel_left
    (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x => (s - x) * Real.sin (ω * x) / ω - Real.cos (ω * x) / ω ^ 2)
      ((s - x) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => s - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x :=
    (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x))
      (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x))
      (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).sub (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp [hω]; ring)

private theorem research9_hasDerivAt_kernel_right
    (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x => (x - s) * Real.sin (ω * x) / ω + Real.cos (ω * x) / ω ^ 2)
      ((x - s) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - s) 1 x := by
    simpa using (hasDerivAt_id x).sub_const s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x :=
    (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x))
      (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x))
      (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).add (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp [hω]; ring)

/-- Exact absolute-distance kernel for an arbitrary nonzero cosine frequency. -/
theorem research9_abs_cos_kernel_eq
    (ω s : ℝ) (hω : ω ≠ 0)
    (hs1 : -(1 : ℝ) / 2 ≤ s) (hs2 : s ≤ 1 / 2) :
    (∫ x in (-(1 : ℝ) / 2)..(1 / 2),
        |s - x| * Real.cos (ω * x))
      = Real.sin (ω / 2) / ω
        + 2 * Real.cos (ω / 2) / ω ^ 2
        - 2 * Real.cos (ω * s) / ω ^ 2 := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable
      (fun x => |s - x| * Real.cos (ω * x)) volume a b := fun a b =>
    Continuous.intervalIntegrable (by fun_prop) a b
  have hsplit :
      (∫ x in (-(1 : ℝ) / 2)..(1 / 2), |s - x| * Real.cos (ω * x))
        = (∫ x in (-(1 : ℝ) / 2)..s, |s - x| * Real.cos (ω * x))
          + ∫ x in s..(1 / 2), |s - x| * Real.cos (ω * x) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
  have hleft :
      (∫ x in (-(1 : ℝ) / 2)..s, |s - x| * Real.cos (ω * x))
        = ∫ x in (-(1 : ℝ) / 2)..s, (s - x) * Real.cos (ω * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs1] at hx
    rw [abs_of_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ s - x)]
  have hleft2 :
      (∫ x in (-(1 : ℝ) / 2)..s, (s - x) * Real.cos (ω * x))
        = ((s - s) * Real.sin (ω * s) / ω - Real.cos (ω * s) / ω ^ 2)
          - ((s - (-(1 : ℝ) / 2)) * Real.sin (ω * (-(1 : ℝ) / 2)) / ω
              - Real.cos (ω * (-(1 : ℝ) / 2)) / ω ^ 2) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => research9_hasDerivAt_kernel_left ω s hω x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hright :
      (∫ x in s..(1 / 2), |s - x| * Real.cos (ω * x))
        = ∫ x in s..(1 / 2), (x - s) * Real.cos (ω * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs2] at hx
    rw [abs_of_nonpos (by linarith [hx.1] : s - x ≤ 0), neg_sub]
  have hright2 :
      (∫ x in s..(1 / 2), (x - s) * Real.cos (ω * x))
        = (((1 : ℝ) / 2 - s) * Real.sin (ω * (1 / 2)) / ω
            + Real.cos (ω * (1 / 2)) / ω ^ 2)
          - ((s - s) * Real.sin (ω * s) / ω + Real.cos (ω * s) / ω ^ 2) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => research9_hasDerivAt_kernel_right ω s hω x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hsplit, hleft, hleft2, hright, hright2]
  have hp : ω * (1 / 2 : ℝ) = ω / 2 := by ring
  have hm : ω * (-(1 : ℝ) / 2) = -(ω / 2) := by ring
  rw [hp, hm, Real.sin_neg, Real.cos_neg]
  field_simp [hω]
  ring

/-- Specialized kernel for the nonzero integer mode `cos(2πns)`. -/
theorem research9_integer_cos_kernel_eq
    (n : ℕ) (hn : 0 < n) (s : ℝ)
    (hs1 : -(1 : ℝ) / 2 ≤ s) (hs2 : s ≤ 1 / 2) :
    (∫ x in (-(1 : ℝ) / 2)..(1 / 2),
        |s - x| * Real.cos ((2 * Real.pi * n) * x))
      = (((-1 : ℝ) ^ n) - Real.cos ((2 * Real.pi * n) * s)) /
          (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hω : (2 * Real.pi * (n : ℝ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hn0
  have h := research9_abs_cos_kernel_eq
    (2 * Real.pi * (n : ℝ)) s hω hs1 hs2
  have hhalf : (2 * Real.pi * (n : ℝ)) / 2 = (n : ℝ) * Real.pi := by ring
  rw [hhalf, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at h
  rw [h]
  field_simp [Real.pi_ne_zero, hn0]
  ring

/-- Integer cosine modes have exactly `1/2` squared mass on the unit core. -/
theorem research9_integer_cos_sq_integral
    (n : ℕ) (hn : 0 < n) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        Real.cos ((2 * Real.pi * n) * s) ^ 2) = 1 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hω : (2 * Real.pi * (n : ℝ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hn0
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hω,
    integral_cos_sq, smul_eq_mul]
  have hp : (2 * Real.pi * (n : ℝ)) * (1 / 2) = (n : ℝ) * Real.pi := by ring
  have hm : (2 * Real.pi * (n : ℝ)) * (-(1 : ℝ) / 2) = -((n : ℝ) * Real.pi) := by ring
  rw [hp, hm, Real.sin_neg, Real.cos_neg,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  field_simp [Real.pi_ne_zero, hn0]
  ring

/-- Distinct positive integer cosine modes are orthogonal on the unit core. -/
theorem research9_integer_cos_orthogonal
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        Real.cos ((2 * Real.pi * n) * s) *
          Real.cos ((2 * Real.pi * m) * s)) = 0 := by
  have hnmR : (n : ℝ) - (m : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hsumR : (n : ℝ) + (m : ℝ) ≠ 0 := by positivity
  have hsub :
      2 * Real.pi * (n : ℝ) - 2 * Real.pi * (m : ℝ) ≠ 0 := by
    rw [show 2 * Real.pi * (n : ℝ) - 2 * Real.pi * (m : ℝ) =
      2 * Real.pi * ((n : ℝ) - (m : ℝ)) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnmR
  have hadd :
      2 * Real.pi * (n : ℝ) + 2 * Real.pi * (m : ℝ) ≠ 0 := by
    rw [show 2 * Real.pi * (n : ℝ) + 2 * Real.pi * (m : ℝ) =
      2 * Real.pi * ((n : ℝ) + (m : ℝ)) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hsumR
  rw [research9_integral_cos_mul_cos _ _ hsub hadd]
  have hargSub :
      (2 * Real.pi * (n : ℝ) - 2 * Real.pi * (m : ℝ)) / 2 =
        (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * Real.pi := by
    push_cast
    ring
  have hargAdd :
      (2 * Real.pi * (n : ℝ) + 2 * Real.pi * (m : ℝ)) / 2 =
        (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hargSub, hargAdd, Real.sin_int_mul_pi, Real.sin_int_mul_pi]
  ring

end HurtadoZeta23
