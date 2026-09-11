import HurtadoZeta23.V21KernelClosedForm
import HurtadoZeta23.V20KernelSignedAnalytic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The single profile-dependent constant left after normalizing the kernel. -/
def v21C : ℝ :=
  Real.cos v21A / (Real.sqrt 2 * Real.sin v21A)

/-- Normalized sinc value of the optimal profile at its intrinsic phase. -/
def v21SincA : ℝ := Real.sin v21A / v21A

lemma v21_A_sq : v21A ^ 2 = (1 / 2 : ℝ) := by
  unfold v21A
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma v21_A_pow3 : v21A ^ 3 = v21A / 2 := by
  calc
    v21A ^ 3 = v21A * v21A ^ 2 := by ring
    _ = v21A / 2 := by rw [v21_A_sq]; ring

lemma v21_A_pow4 : v21A ^ 4 = (1 / 4 : ℝ) := by
  calc
    v21A ^ 4 = (v21A ^ 2) ^ 2 := by ring
    _ = (1 / 4 : ℝ) := by rw [v21_A_sq]; norm_num

lemma v21_A_pow5 : v21A ^ 5 = v21A / 4 := by
  calc
    v21A ^ 5 = v21A * v21A ^ 4 := by ring
    _ = v21A / 4 := by rw [v21_A_pow4]; ring

lemma v21_A_pow6 : v21A ^ 6 = (1 / 8 : ℝ) := by
  calc
    v21A ^ 6 = (v21A ^ 2) ^ 3 := by ring
    _ = (1 / 8 : ℝ) := by rw [v21_A_sq]; norm_num

lemma v21_A_pow7 : v21A ^ 7 = v21A / 8 := by
  calc
    v21A ^ 7 = v21A * v21A ^ 6 := by ring
    _ = v21A / 8 := by rw [v21_A_pow6]; ring

lemma v21_A_pow8 : v21A ^ 8 = (1 / 16 : ℝ) := by
  calc
    v21A ^ 8 = (v21A ^ 2) ^ 4 := by ring
    _ = (1 / 16 : ℝ) := by rw [v21_A_sq]; norm_num

lemma v21_A_pow9 : v21A ^ 9 = v21A / 16 := by
  calc
    v21A ^ 9 = v21A * v21A ^ 8 := by ring
    _ = v21A / 16 := by rw [v21_A_pow8]; ring

lemma v21_A_pow10 : v21A ^ 10 = (1 / 32 : ℝ) := by
  calc
    v21A ^ 10 = (v21A ^ 2) ^ 5 := by ring
    _ = (1 / 32 : ℝ) := by rw [v21_A_sq]; norm_num

lemma v21_sinA_pos : 0 < Real.sin v21A := by
  have hs := Zeta23.ThmD.sin_theta_pos (lam := (1 : ℝ)) one_pos le_rfl
  rw [Zeta23.ThmD.theta_one] at hs
  simpa [v21A] using hs

lemma v21_sincA_pos : 0 < v21SincA := by
  unfold v21SincA
  exact div_pos v21_sinA_pos v21_A_pos

/-- The zero-frequency normalization equals the profile sinc. -/
lemma v21_sincA_eq_K0 :
    v21SincA = Real.sqrt 2 * Real.sin v21A := by
  unfold v21SincA
  apply (div_eq_iff v21_A_pos.ne').2
  have hsqrtA : Real.sqrt 2 * v21A = 1 := by
    unfold v21A
    exact mul_inv_cancel₀ (by positivity)
  calc
    Real.sin v21A = 1 * Real.sin v21A := by ring
    _ = (Real.sqrt 2 * v21A) * Real.sin v21A := by rw [hsqrtA]
    _ = (Real.sqrt 2 * Real.sin v21A) * v21A := by ring

lemma v21_C_eq_cos_div_sinc :
    v21C = Real.cos v21A / v21SincA := by
  unfold v21C
  rw [v21_sincA_eq_K0]

/-- High-accuracy rational upper enclosure for the profile sinc, derived from
the v20 Taylor theorem rather than an external interval oracle. -/
lemma v21_sincA_upper :
    v21SincA ≤ (5334193 / 5806080 : ℝ) := by
  have hs := v20_sin_upper9 (x := v21A) v21_A_pos.le (le_of_lt v21_A_lt_one)
  unfold v21SincA
  apply (div_le_iff₀ v21_A_pos).2
  calc
    Real.sin v21A ≤
        v21A - v21A^3 / 6 + v21A^5 / 120 - v21A^7 / 5040
          + v21A^9 / 362880 := hs
    _ = (5334193 / 5806080 : ℝ) * v21A := by
      rw [v21_A_pow3, v21_A_pow5, v21_A_pow7, v21_A_pow9]
      ring

/-- High-accuracy rational lower enclosure for `cos(1/sqrt 2)`. -/
lemma v21_cosA_lower :
    (88280819 / 116121600 : ℝ) ≤ Real.cos v21A := by
  have hc := v20_cos_lower10 (x := v21A) v21_A_pos.le (le_of_lt v21_A_lt_one)
  calc
    (88280819 / 116121600 : ℝ) =
        1 - v21A^2 / 2 + v21A^4 / 24 - v21A^6 / 720
          + v21A^8 / 40320 - v21A^10 / 3628800 := by
      rw [v21_A_sq, v21_A_pow4, v21_A_pow6, v21_A_pow8, v21_A_pow10]
      norm_num
    _ ≤ Real.cos v21A := hc

/-- Nearly sharp rational lower bound for the sole profile constant `C`. -/
lemma v21_C_lower :
    (88280819 / 106683860 : ℝ) ≤ v21C := by
  rw [v21_C_eq_cos_div_sinc]
  apply (le_div_iff₀ v21_sincA_pos).2
  have hscaled := mul_le_mul_of_nonneg_left v21_sincA_upper
    (show (0 : ℝ) ≤ 88280819 / 106683860 by norm_num)
  have hexact :
      (88280819 / 106683860 : ℝ) * (5334193 / 5806080 : ℝ) =
        (88280819 / 116121600 : ℝ) := by
    norm_num
  rw [hexact] at hscaled
  exact hscaled.trans v21_cosA_lower

/-- After normalization, the kernel has only one profile constant and the
exact algebraic denominator `B^2 - 1/2`. -/
theorem v21_limitingk_normalized {x : ℝ}
    (hx : v21A < v21B x) :
    limitingk x =
      (v21C * v21B x * Real.sin (v21B x) -
          (1 / 2 : ℝ) * Real.cos (v21B x)) /
        ((v21B x) ^ 2 - (1 / 2 : ℝ)) := by
  unfold limitingk
  rw [v21_limitingK_closed hx, limitingK_zero_closed, v21_A_sq]
  rw [← v21_sincA_eq_K0]
  rw [v21_C_eq_cos_div_sinc]
  have hsinc : v21SincA ≠ 0 := ne_of_gt v21_sincA_pos
  have hden : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0 := by
    have hBpos : 0 < v21B x := lt_trans v21_A_pos hx
    have hfac := mul_pos (sub_pos.mpr hx) (add_pos hBpos v21_A_pos)
    rw [v21_A_sq] at hfac
    nlinarith
  have hAover : v21A / Real.sqrt 2 = (1 / 2 : ℝ) := by
    apply (div_eq_iff (by positivity : Real.sqrt 2 ≠ 0)).2
    nlinarith [v21_sqrt_two_half]
  have hsincform :
      v21SincA = Real.sqrt 2 * Real.sin v21A := v21_sincA_eq_K0
  unfold v21SincA at hsinc
  field_simp [hsinc, hden, v21_A_pos.ne']
  have hsqrtA : Real.sqrt 2 * v21A = 1 := by
    unfold v21A
    exact mul_inv_cancel₀ (by positivity)
  nlinarith [hsqrtA, v21_A_sq]

/-- Squared normalized form used in the finite hard-core certificate. -/
theorem v21_limitingWeight_normalized {x : ℝ}
    (hx : v21A < v21B x) :
    limitingWeight x =
      ((v21C * v21B x * Real.sin (v21B x) -
          (1 / 2 : ℝ) * Real.cos (v21B x)) /
        ((v21B x) ^ 2 - (1 / 2 : ℝ))) ^ 2 := by
  unfold limitingWeight
  rw [v21_limitingk_normalized hx]

end HurtadoZeta23
