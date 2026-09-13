import HurtadoZeta23.V26PhaseGeometry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- `arctan` is globally 1-Lipschitz, obtained directly from its exact
derivative `1/(1+x^2)`. -/
lemma v26_arctan_diff_abs_le (u v : ℝ) :
    |Real.arctan u - Real.arctan v| ≤ |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := Real.arctan) (C := (1 : ℝ))
    (x := v) (y := u)
    (fun z _ => Real.differentiableAt_arctan z)
    (fun z _ => by
      rw [Real.deriv_arctan, Real.norm_eq_abs]
      have hden : (1 : ℝ) ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
      have hpos : (0 : ℝ) < 1 + z ^ 2 := lt_of_lt_of_le zero_lt_one hden
      rw [abs_of_nonneg (one_div_nonneg.mpr hpos.le)]
      have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
      simpa using hrec)
    convex_univ (by simp) (by simp)
  simpa [Real.norm_eq_abs] using h

/-- On `[L,∞)`, the reciprocal phase shift has the elementary Lipschitz
constant `c/L^2`. -/
lemma v26_reciprocal_shift_abs_le {c L x r : ℝ}
    (hc : 0 ≤ c) (hL : 0 < L) (hLx : L ≤ x) (hLr : L ≤ r) :
    |c / x - c / r| ≤ (c / L ^ 2) * |x - r| := by
  have hx : 0 < x := hL.trans_le hLx
  have hr : 0 < r := hL.trans_le hLr
  have hxr : 0 < x * r := mul_pos hx hr
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hprod : L ^ 2 ≤ x * r := by
    calc
      L ^ 2 = L * L := by ring
      _ ≤ x * L := mul_le_mul_of_nonneg_right hLx hL.le
      _ ≤ x * r := mul_le_mul_of_nonneg_left hLr hx.le
  have hid : c / x - c / r = c * (r - x) / (x * r) := by
    field_simp [hx.ne', hr.ne']
    ring
  have hrec : 1 / (x * r) ≤ 1 / L ^ 2 :=
    one_div_le_one_div_of_le hL2 hprod
  have hcoef : c / (x * r) ≤ c / L ^ 2 := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrec hc
  rw [hid, abs_div, abs_mul, abs_of_nonneg hc, abs_of_pos hxr, abs_sub_comm]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- Upper phase distortion on the positive half-line.  Together with
`v26_phase_distance_lower`, this gives exactly the two-sided phase control
used by the rational kernel minorants. -/
theorem v26_phase_distance_upper {c L x r : ℝ}
    (hc : 0 ≤ c) (hL : 0 < L) (hLx : L ≤ x) (hLr : L ≤ r) :
    |v26PhaseWith c x - v26PhaseWith c r| ≤
      (1 + c / (Real.pi * L ^ 2)) * |x - r| := by
  have hatan := v26_arctan_diff_abs_le (c / x) (c / r)
  have hfrac := v26_reciprocal_shift_abs_le hc hL hLx hLr
  have hpi : 0 < (1 / Real.pi : ℝ) := one_div_pos.mpr Real.pi_pos
  have hphase :
      v26PhaseWith c x - v26PhaseWith c r =
        (x - r) - (1 / Real.pi) *
          (Real.arctan (c / x) - Real.arctan (c / r)) := by
    unfold v26PhaseWith
    ring
  rw [hphase]
  calc
    |(x - r) - (1 / Real.pi) *
        (Real.arctan (c / x) - Real.arctan (c / r))|
        ≤ |x - r| + |-(1 / Real.pi) *
            (Real.arctan (c / x) - Real.arctan (c / r))| := by
          convert abs_add_le (x - r)
            (-(1 / Real.pi) * (Real.arctan (c / x) - Real.arctan (c / r))) using 1 <;> ring
    _ = |x - r| + (1 / Real.pi) *
          |Real.arctan (c / x) - Real.arctan (c / r)| := by
          rw [abs_mul, abs_neg, abs_of_pos hpi]
    _ ≤ |x - r| + (1 / Real.pi) * |c / x - c / r| := by
          gcongr
    _ ≤ |x - r| + (1 / Real.pi) * ((c / L ^ 2) * |x - r|) := by
          gcongr
    _ = (1 + c / (Real.pi * L ^ 2)) * |x - r| := by
          field_simp [Real.pi_ne_zero, hL.ne']
          ring

end HurtadoZeta23
