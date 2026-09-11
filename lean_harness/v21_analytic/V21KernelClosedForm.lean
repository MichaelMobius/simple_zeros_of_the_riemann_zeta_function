import HurtadoZeta23.ExternalCertificateFrontier
import HurtadoZeta23.V17KernelMonotonicity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

open Real intervalIntegral

namespace HurtadoZeta23

/-- Half of the intrinsic frequency of the optimal Montgomery--Taylor profile. -/
def v21A : ℝ := (Real.sqrt 2)⁻¹

/-- The external Fourier phase at normalized separation `x`. -/
def v21B (x : ℝ) : ℝ := Real.pi * x

lemma v21_A_pos : 0 < v21A := by
  unfold v21A
  positivity

lemma v21_A_lt_one : v21A < 1 := by
  exact Zeta23.ThmD.sqrt_two_inv_lt_one

lemma v21_sqrt_two_half : Real.sqrt 2 / 2 = v21A := by
  have h := Zeta23.ThmD.sqrt2_mul_half (lam := (1 : ℝ))
  rw [Zeta23.ThmD.theta_one] at h
  unfold v21A
  nlinarith

/-- Every argument occurring in the v21 hard core lies beyond the only
removable singularity of the elementary kernel formula. -/
lemma v21_A_lt_B_of_cert_lt {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    v21A < v21B x := by
  have hA : v21A < 1 := v21_A_lt_one
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hx' : (89 / 100 : ℝ) < x := by
    simpa [v17KernelCertPoint] using hx
  unfold v21B
  have hx0 : 0 < x := by norm_num at hx' ⊢; linarith
  nlinarith

/-- Elementary symmetric integral. -/
lemma v21_integral_cos_symm {c : ℝ} (hc : c ≠ 0) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) =
      2 * Real.sin (c / 2) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos, smul_eq_mul]
  rw [show c * (-(1 : ℝ) / 2) = -(c / 2) by ring,
      show c * (1 / 2 : ℝ) = c / 2 by ring, Real.sin_neg]
  field_simp [hc]
  ring

/-- Product-to-sum evaluation on the symmetric unit interval. -/
lemma v21_integral_cos_product {a b : ℝ}
    (hm : a - b ≠ 0) (hp : a + b ≠ 0) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2),
        Real.cos (a * t) * Real.cos (b * t)) =
      Real.sin ((a - b) / 2) / (a - b) +
        Real.sin ((a + b) / 2) / (a + b) := by
  calc
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (a * t) * Real.cos (b * t)) =
        ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
          (Real.cos ((a - b) * t) + Real.cos ((a + b) * t)) / 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have h := Real.two_mul_cos_mul_cos (a * t) (b * t)
      rw [show a * t - b * t = (a - b) * t by ring,
          show a * t + b * t = (a + b) * t by ring] at h
      linarith
    _ = ((∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos ((a - b) * t)) +
          (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos ((a + b) * t))) / 2 := by
      rw [intervalIntegral.integral_div]
      rw [intervalIntegral.integral_add]
      · exact (by fun_prop : Continuous (fun t : ℝ => Real.cos ((a - b) * t))).intervalIntegrable _ _
      · exact (by fun_prop : Continuous (fun t : ℝ => Real.cos ((a + b) * t))).intervalIntegrable _ _
    _ = Real.sin ((a - b) / 2) / (a - b) +
          Real.sin ((a + b) / 2) / (a + b) := by
      rw [v21_integral_cos_symm hm, v21_integral_cos_symm hp]
      ring

/-- Integral-free sinc representation of the limiting overlap. -/
theorem v21_limitingK_sinc_formula {x : ℝ}
    (hx : v21A < v21B x) :
    limitingK x =
      Real.sin (v21A - v21B x) / (2 * (v21A - v21B x)) +
      Real.sin (v21A + v21B x) / (2 * (v21A + v21B x)) := by
  have hBpos : 0 < v21B x := lt_trans v21_A_pos hx
  have hm : Real.sqrt 2 - 2 * v21B x ≠ 0 := by
    have hs := v21_sqrt_two_half
    intro hzero
    have : v21A = v21B x := by nlinarith
    exact (ne_of_lt hx) this
  have hp : Real.sqrt 2 + 2 * v21B x ≠ 0 := by
    positivity
  have hprod := v21_integral_cos_product
    (a := Real.sqrt 2) (b := 2 * v21B x) hm hp
  have hraw :
      limitingK x =
        Real.sin ((Real.sqrt 2 - 2 * v21B x) / 2) /
            (Real.sqrt 2 - 2 * v21B x) +
          Real.sin ((Real.sqrt 2 + 2 * v21B x) / 2) /
            (Real.sqrt 2 + 2 * v21B x) := by
    unfold limitingK Zeta23.ThmD.vStar
    simp only [mul_one]
    calc
      (∫ t in (-(1 : ℝ) / 2)..(1 / 2),
          Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)) =
          ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
            Real.cos (Real.sqrt 2 * t) * Real.cos ((2 * v21B x) * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        unfold v21B
        ring_nf
      _ = _ := hprod
  have hminusHalf :
      (Real.sqrt 2 - 2 * v21B x) / 2 = v21A - v21B x := by
    nlinarith [v21_sqrt_two_half]
  have hplusHalf :
      (Real.sqrt 2 + 2 * v21B x) / 2 = v21A + v21B x := by
    nlinarith [v21_sqrt_two_half]
  have hminusDen :
      Real.sqrt 2 - 2 * v21B x = 2 * (v21A - v21B x) := by
    nlinarith [v21_sqrt_two_half]
  have hplusDen :
      Real.sqrt 2 + 2 * v21B x = 2 * (v21A + v21B x) := by
    nlinarith [v21_sqrt_two_half]
  rw [hraw, hminusHalf, hplusHalf, hminusDen, hplusDen]

/-- Rational-trigonometric closed form.  On the hard core its denominator is
strictly positive, so the integral has disappeared without introducing any
case split or numerical oracle. -/
theorem v21_limitingK_closed {x : ℝ}
    (hx : v21A < v21B x) :
    limitingK x =
      (v21B x * Real.cos v21A * Real.sin (v21B x) -
          v21A * Real.sin v21A * Real.cos (v21B x)) /
        ((v21B x) ^ 2 - v21A ^ 2) := by
  rw [v21_limitingK_sinc_formula hx, Real.sin_sub, Real.sin_add]
  have hBpos : 0 < v21B x := lt_trans v21_A_pos hx
  have hm : v21A - v21B x ≠ 0 := ne_of_lt (sub_neg.mpr hx)
  have hp : v21A + v21B x ≠ 0 := ne_of_gt (add_pos v21_A_pos hBpos)
  have hdenpos : 0 < (v21B x) ^ 2 - v21A ^ 2 := by
    have hfac := mul_pos (sub_pos.mpr hx) (add_pos hBpos v21_A_pos)
    nlinarith
  field_simp [hm, hp, ne_of_gt hdenpos]
  ring

/-- Closed form for the normalized squared weight used by every pair term. -/
theorem v21_limitingWeight_closed {x : ℝ}
    (hx : v21A < v21B x) :
    limitingWeight x =
      (((v21B x * Real.cos v21A * Real.sin (v21B x) -
          v21A * Real.sin v21A * Real.cos (v21B x)) /
        ((v21B x) ^ 2 - v21A ^ 2)) /
        (Real.sqrt 2 * Real.sin v21A)) ^ 2 := by
  unfold limitingWeight limitingk
  rw [v21_limitingK_closed hx, limitingK_zero_closed]
  rfl

/-- Hard-core specialization: all weight evaluations can use the closed form. -/
theorem v21_limitingWeight_closed_of_cert_lt {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    limitingWeight x =
      (((v21B x * Real.cos v21A * Real.sin (v21B x) -
          v21A * Real.sin v21A * Real.cos (v21B x)) /
        ((v21B x) ^ 2 - v21A ^ 2)) /
        (Real.sqrt 2 * Real.sin v21A)) ^ 2 := by
  exact v21_limitingWeight_closed (v21_A_lt_B_of_cert_lt hx)

end HurtadoZeta23
