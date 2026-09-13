import HurtadoZeta23.V21TaylorTools
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The seventh-degree alternating sine polynomial used by the v26 phase
minorants. -/
def v26P7 (x : ℝ) : ℝ :=
  x - x^3 / 6 + x^5 / 120 - x^7 / 5040

/-- The sixth-degree alternating cosine polynomial used after halving the
phase. -/
def v26C6 (x : ℝ) : ℝ :=
  1 - x^2 / 2 + x^4 / 24 - x^6 / 720

/-- On `[0,1]` the cosine polynomial retained in the double-angle argument is
nonnegative. -/
lemma v26_C6_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ v26C6 x := by
  have hx2 : x ^ 2 ≤ (1 : ℝ) := pow_le_one₀ hx0 hx1
  have hx6 : x ^ 6 ≤ (1 : ℝ) := pow_le_one₀ hx0 hx1
  have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx0 4
  unfold v26C6
  nlinarith

/-- Exact polynomial identity behind the extension of the Taylor lower bound
from `[0,1]` to `[0,8/5]`. -/
lemma v26_double_angle_polynomial_identity (x : ℝ) :
    2 * v26P7 (x / 2) * v26C6 (x / 2) - v26P7 x =
      x^9 * (x^4 - 288 * x^2 + 39360) / 14863564800 := by
  unfold v26P7 v26C6
  ring

/-- The numerator in the exact double-angle remainder is nonnegative on the
phase range needed by the rational basin proof. -/
lemma v26_double_angle_remainder_nonneg {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ (8 / 5 : ℝ)) :
    0 ≤ x^9 * (x^4 - 288 * x^2 + 39360) / 14863564800 := by
  have hplus : 0 ≤ (8 / 5 : ℝ) + x := by linarith
  have hfac : 0 ≤ ((8 / 5 : ℝ) - x) * ((8 / 5 : ℝ) + x) :=
    mul_nonneg (sub_nonneg.mpr hx1) hplus
  have hx2 : x^2 ≤ (64 / 25 : ℝ) := by
    nlinarith
  have hx4 : 0 ≤ x^4 := pow_nonneg hx0 4
  have hpoly : 0 ≤ x^4 - 288 * x^2 + 39360 := by
    nlinarith
  exact div_nonneg (mul_nonneg (pow_nonneg hx0 9) hpoly) (by norm_num)

/-- Four-term alternating Taylor lower bound for sine on the larger interval
`[0,8/5]` required by the v26 phase displacement.  The proof uses only the
already formalized `[0,1]` sine/cosine bounds, the double-angle identity, and
exact polynomial arithmetic. -/
theorem v26_sin_lower7_upto_eight_fifths {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ (8 / 5 : ℝ)) :
    v26P7 x ≤ Real.sin x := by
  let y : ℝ := x / 2
  have hy0 : 0 ≤ y := by
    dsimp [y]
    linarith
  have hy1 : y ≤ 1 := by
    dsimp [y]
    linarith
  have hs : v26P7 y ≤ Real.sin y := by
    simpa [v26P7] using v21_sin_lower7 hy0 hy1
  have hc : v26C6 y ≤ Real.cos y := by
    simpa [v26C6] using v21_cos_lower6 hy0 hy1
  have hC0 : 0 ≤ v26C6 y := v26_C6_nonneg hy0 hy1
  have hsin0 : 0 ≤ Real.sin y := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi hy0
    linarith [Real.two_le_pi]
  have hprod1 :
      v26P7 y * v26C6 y ≤ Real.sin y * v26C6 y :=
    mul_le_mul_of_nonneg_right hs hC0
  have hprod2 :
      Real.sin y * v26C6 y ≤ Real.sin y * Real.cos y :=
    mul_le_mul_of_nonneg_left hc hsin0
  have hprod :
      2 * v26P7 y * v26C6 y ≤ 2 * Real.sin y * Real.cos y := by
    nlinarith
  have hrem := v26_double_angle_remainder_nonneg hx0 hx1
  have hid := v26_double_angle_polynomial_identity x
  have hpoly : v26P7 x ≤ 2 * v26P7 (x / 2) * v26C6 (x / 2) := by
    rw [← hid] at hrem
    linarith
  have hy : x = 2 * y := by
    dsimp [y]
    ring
  have hsin : Real.sin x = 2 * Real.sin y * Real.cos y := by
    rw [hy, Real.sin_two_mul]
  calc
    v26P7 x ≤ 2 * v26P7 (x / 2) * v26C6 (x / 2) := hpoly
    _ = 2 * v26P7 y * v26C6 y := by rfl
    _ ≤ 2 * Real.sin y * Real.cos y := hprod
    _ = Real.sin x := hsin.symm

end HurtadoZeta23
