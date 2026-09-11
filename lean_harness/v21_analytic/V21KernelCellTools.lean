import HurtadoZeta23.V21KernelNormalized
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Positive algebraic denominator of the normalized kernel beyond its
removable singularity. -/
def v21D (x : ℝ) : ℝ := (v21B x) ^ 2 - (1 / 2 : ℝ)

lemma v21_D_pos {x : ℝ} (hx : v21A < v21B x) : 0 < v21D x := by
  unfold v21D
  have hBpos : 0 < v21B x := lt_trans v21_A_pos hx
  have hfac := mul_pos (sub_pos.mpr hx) (add_pos hBpos v21_A_pos)
  have hsq : v21A ^ 2 < (v21B x) ^ 2 := by
    nlinarith [hfac]
  rw [v21_A_sq] at hsq
  nlinarith

/-- Correlation-preserving decomposition used by all cell bounds. -/
theorem v21_limitingk_decomposed {x : ℝ}
    (hx : v21A < v21B x) :
    limitingk x =
      v21C * (v21B x / v21D x) * Real.sin (v21B x) -
      (1 / 2 : ℝ) * (1 / v21D x) * Real.cos (v21B x) := by
  rw [v21_limitingk_normalized hx]
  have hD : v21D x ≠ 0 := ne_of_gt (v21_D_pos hx)
  unfold v21D
  field_simp [hD]

/-- Phase about the integer centre `1`. -/
def v21Phase1 (x : ℝ) : ℝ := Real.pi * (1 - x)

lemma v21_B_eq_pi_sub_phase1 (x : ℝ) :
    v21B x = Real.pi - v21Phase1 x := by
  unfold v21B v21Phase1
  ring

lemma v21_sinB_phase1 (x : ℝ) :
    Real.sin (v21B x) = Real.sin (v21Phase1 x) := by
  rw [v21_B_eq_pi_sub_phase1, Real.sin_pi_sub]

lemma v21_cosB_phase1 (x : ℝ) :
    Real.cos (v21B x) = -Real.cos (v21Phase1 x) := by
  rw [v21_B_eq_pi_sub_phase1, Real.cos_pi_sub]

/-- On the first lobe the normalized kernel is a sum of two positive-shaped
terms; this is the form used for the interval `(0.89,0.95)`. -/
theorem v21_k_phase1 {x : ℝ} (hx : v21A < v21B x) :
    limitingk x =
      v21C * (v21B x / v21D x) * Real.sin (v21Phase1 x) +
      (1 / 2 : ℝ) * (1 / v21D x) * Real.cos (v21Phase1 x) := by
  rw [v21_limitingk_decomposed hx, v21_sinB_phase1, v21_cosB_phase1]
  ring

/-- Phase about the half-integer centre `3/2`. -/
def v21Phase15 (x : ℝ) : ℝ := Real.pi * (x - (3 / 2 : ℝ))

lemma v21_B_eq_phase15 (x : ℝ) :
    v21B x = Real.pi + (Real.pi / 2 + v21Phase15 x) := by
  unfold v21B v21Phase15
  ring

lemma v21_sinB_phase15 (x : ℝ) :
    Real.sin (v21B x) = -Real.cos (v21Phase15 x) := by
  rw [v21_B_eq_phase15]
  simp [Real.sin_add, Real.cos_add]

lemma v21_cosB_phase15 (x : ℝ) :
    Real.cos (v21B x) = Real.sin (v21Phase15 x) := by
  rw [v21_B_eq_phase15]
  simp [Real.sin_add, Real.cos_add]

/-- Signed form on the second lobe. -/
theorem v21_negk_phase15 {x : ℝ} (hx : v21A < v21B x) :
    -limitingk x =
      v21C * (v21B x / v21D x) * Real.cos (v21Phase15 x) +
      (1 / 2 : ℝ) * (1 / v21D x) * Real.sin (v21Phase15 x) := by
  rw [v21_limitingk_decomposed hx, v21_sinB_phase15, v21_cosB_phase15]
  ring

/-- Phase about the half-integer centre `5/2`. -/
def v21Phase25 (x : ℝ) : ℝ := Real.pi * (x - (5 / 2 : ℝ))

lemma v21_B_eq_phase25 (x : ℝ) :
    v21B x = Real.pi + (Real.pi + (Real.pi / 2 + v21Phase25 x)) := by
  unfold v21B v21Phase25
  ring

lemma v21_sinB_phase25 (x : ℝ) :
    Real.sin (v21B x) = Real.cos (v21Phase25 x) := by
  rw [v21_B_eq_phase25]
  simp [Real.sin_add, Real.cos_add]

lemma v21_cosB_phase25 (x : ℝ) :
    Real.cos (v21B x) = -Real.sin (v21Phase25 x) := by
  rw [v21_B_eq_phase25]
  simp [Real.sin_add, Real.cos_add]

/-- Signed form on the third lobe. -/
theorem v21_k_phase25 {x : ℝ} (hx : v21A < v21B x) :
    limitingk x =
      v21C * (v21B x / v21D x) * Real.cos (v21Phase25 x) +
      (1 / 2 : ℝ) * (1 / v21D x) * Real.sin (v21Phase25 x) := by
  rw [v21_limitingk_decomposed hx, v21_sinB_phase25, v21_cosB_phase25]
  ring

/-- The factor `b/(b^2-1/2)` is antitone for `b>1`, proved by direct
cross-multiplication rather than calculus. -/
lemma v21_ratio_factor_lower
    {b u : ℝ} (hb : 1 < b) (hbu : b ≤ u) :
    u / (u ^ 2 - (1 / 2 : ℝ)) ≤
      b / (b ^ 2 - (1 / 2 : ℝ)) := by
  have hu : 1 < u := hb.trans_le hbu
  have hbden : 0 < b ^ 2 - (1 / 2 : ℝ) := by nlinarith [sq_nonneg (b - 1)]
  have huden : 0 < u ^ 2 - (1 / 2 : ℝ) := by nlinarith [sq_nonneg (u - 1)]
  apply (div_le_div_iff₀ huden hbden).2
  have hprod :
      0 ≤ (u - b) * (b * u + (1 / 2 : ℝ)) := by
    exact mul_nonneg (sub_nonneg.mpr hbu) (by nlinarith)
  nlinarith

/-- The reciprocal denominator factor is likewise antitone for positive
frequencies. -/
lemma v21_recip_factor_lower
    {b u : ℝ} (hb : 1 < b) (hbu : b ≤ u) :
    1 / (u ^ 2 - (1 / 2 : ℝ)) ≤
      1 / (b ^ 2 - (1 / 2 : ℝ)) := by
  have hu : 1 < u := hb.trans_le hbu
  have hbden : 0 < b ^ 2 - (1 / 2 : ℝ) := by nlinarith [sq_nonneg (b - 1)]
  have huden : 0 < u ^ 2 - (1 / 2 : ℝ) := by nlinarith [sq_nonneg (u - 1)]
  exact one_div_le_one_div_of_le hbden (by nlinarith [sq_nonneg (u - b)])

/-- Rational π bounds reused throughout the finite cell proof. -/
lemma v21_pi_lower : (31415926 / 10000000 : ℝ) < Real.pi := by
  nlinarith [Real.pi_gt_d20]

lemma v21_pi_upper : Real.pi < (31415927 / 10000000 : ℝ) := by
  nlinarith [Real.pi_lt_d20]

/-- Convert a signed lower bound on `k` into the squared weight bound. -/
lemma v21_weight_lower_of_k_lower {x q : ℝ}
    (hq0 : 0 ≤ q) (hk : q ≤ limitingk x) :
    q ^ 2 ≤ limitingWeight x := by
  unfold limitingWeight
  exact pow_le_pow_left₀ hq0 hk 2

/-- The analogous conversion on a negative lobe. -/
lemma v21_weight_lower_of_negk_lower {x q : ℝ}
    (hq0 : 0 ≤ q) (hk : q ≤ -limitingk x) :
    q ^ 2 ≤ limitingWeight x := by
  unfold limitingWeight
  have hs := pow_le_pow_left₀ hq0 hk 2
  simpa using hs

end HurtadoZeta23
