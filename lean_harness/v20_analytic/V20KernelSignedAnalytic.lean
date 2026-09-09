import HurtadoZeta23.LimitingKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace HurtadoZeta23

/-!
# Analytic replacement for the v17 signed kernel enclosure

The target is the strict inequality
`171389 / 1000000 < limitingk (89/100)`.
No interval oracle is used in the intended final proof.  A separate tiny bridge
will translate this theorem into `V17KernelSignedCertPointClaim` after the
analytic module is closed.
-/

private def sinTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)

private def cosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n).factorial : ℝ)

private lemma sinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (sinTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold sinTerm
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden :
      ((2 * n + 1).factorial : ℝ) ≤ ((2 * (n + 1) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)
  calc
    x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ)
        ≤ x ^ (2 * n + 1) / ((2 * (n + 1) + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hx0 _) (by positivity) hden

private lemma cosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (cosTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold cosTerm
  have hpow : x ^ (2 * (n + 1)) ≤ x ^ (2 * n) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden :
      ((2 * n).factorial : ℝ) ≤ ((2 * (n + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n ≤ 2 * (n + 1))
  calc
    x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)
        ≤ x ^ (2 * n) / ((2 * (n + 1)).factorial : ℝ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hx0 _) (by positivity) hden

/-- Four-term alternating Taylor lower bound for sine on `[0,1]`. -/
lemma v20_sin_lower7 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x^3 / 6 + x^5 / 120 - x^7 / 5040 ≤ Real.sin x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * sinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [sinTerm] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (sinTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 2
  norm_num [sinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Four-term alternating Taylor lower bound for cosine on `[0,1]`. -/
lemma v20_cos_lower6 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x^2 / 2 + x^4 / 24 - x^6 / 720 ≤ Real.cos x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * cosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [cosTerm] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (cosTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 2
  norm_num [cosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Six-term alternating lower bound for cosine, used at `1/sqrt 2`. -/
lemma v20_cos_lower10 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x^2 / 2 + x^4 / 24 - x^6 / 720 + x^8 / 40320 - x^10 / 3628800
      ≤ Real.cos x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * cosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [cosTerm] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (cosTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 3
  norm_num [cosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Five-term alternating upper bound for sine, used at `1/sqrt 2`. -/
lemma v20_sin_upper9 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x^3 / 6 + x^5 / 120 - x^7 / 5040 + x^9 / 362880 := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * sinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [sinTerm] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (sinTerm_antitone hx0 hx1).tendsto_le_alternating_series ht 2
  norm_num [sinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

private def v20A : ℝ := (Real.sqrt 2)⁻¹
private def v20Theta : ℝ := (11 / 100 : ℝ) * Real.pi
private def v20B : ℝ := (89 / 100 : ℝ) * Real.pi

private lemma v20_pi_lower :
    (31415926 / 10000000 : ℝ) < Real.pi := by
  nlinarith [Real.pi_gt_d20]

private lemma v20_pi_upper :
    Real.pi < (31415927 / 10000000 : ℝ) := by
  nlinarith [Real.pi_lt_d20]

private lemma v20_A_pos : 0 < v20A := by
  unfold v20A
  positivity

private lemma v20_A_le_one : v20A ≤ 1 := by
  exact le_of_lt Zeta23.ThmD.sqrt_two_inv_lt_one

private lemma v20_A_sq : v20A ^ 2 = (1 / 2 : ℝ) := by
  unfold v20A
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma v20_A_pow3 : v20A ^ 3 = v20A / 2 := by
  calc
    v20A ^ 3 = v20A * v20A ^ 2 := by ring
    _ = v20A / 2 := by rw [v20_A_sq]; ring

private lemma v20_A_pow4 : v20A ^ 4 = (1 / 4 : ℝ) := by
  calc
    v20A ^ 4 = (v20A ^ 2) ^ 2 := by ring
    _ = (1 / 4 : ℝ) := by rw [v20_A_sq]; norm_num

private lemma v20_A_pow5 : v20A ^ 5 = v20A / 4 := by
  calc
    v20A ^ 5 = v20A * v20A ^ 4 := by ring
    _ = v20A / 4 := by rw [v20_A_pow4]; ring

private lemma v20_A_pow6 : v20A ^ 6 = (1 / 8 : ℝ) := by
  calc
    v20A ^ 6 = (v20A ^ 2) ^ 3 := by ring
    _ = (1 / 8 : ℝ) := by rw [v20_A_sq]; norm_num

private lemma v20_A_pow7 : v20A ^ 7 = v20A / 8 := by
  calc
    v20A ^ 7 = v20A * v20A ^ 6 := by ring
    _ = v20A / 8 := by rw [v20_A_pow6]; ring

private lemma v20_A_pow8 : v20A ^ 8 = (1 / 16 : ℝ) := by
  calc
    v20A ^ 8 = (v20A ^ 2) ^ 4 := by ring
    _ = (1 / 16 : ℝ) := by rw [v20_A_sq]; norm_num

private lemma v20_A_pow9 : v20A ^ 9 = v20A / 16 := by
  calc
    v20A ^ 9 = v20A * v20A ^ 8 := by ring
    _ = v20A / 16 := by rw [v20_A_pow8]; ring

private lemma v20_A_pow10 : v20A ^ 10 = (1 / 32 : ℝ) := by
  calc
    v20A ^ 10 = (v20A ^ 2) ^ 5 := by ring
    _ = (1 / 32 : ℝ) := by rw [v20_A_sq]; norm_num

/-- Rational lower bound for `sin(1/sqrt 2)/(1/sqrt 2)`. -/
private lemma v20_sincA_lower :
    (37043 / 40320 : ℝ) ≤ Real.sin v20A / v20A := by
  have hs := v20_sin_lower7 (x := v20A) v20_A_pos.le v20_A_le_one
  apply (le_div_iff₀ v20_A_pos).2
  calc
    (37043 / 40320 : ℝ) * v20A =
        v20A - v20A^3 / 6 + v20A^5 / 120 - v20A^7 / 5040 := by
      rw [v20_A_pow3, v20_A_pow5, v20_A_pow7]
      ring
    _ ≤ Real.sin v20A := hs

/-- Rational upper bound for `sin(1/sqrt 2)/(1/sqrt 2)`. -/
private lemma v20_sincA_upper :
    Real.sin v20A / v20A ≤ (5334193 / 5806080 : ℝ) := by
  have hs := v20_sin_upper9 (x := v20A) v20_A_pos.le v20_A_le_one
  apply (div_le_iff₀ v20_A_pos).2
  calc
    Real.sin v20A ≤
        v20A - v20A^3 / 6 + v20A^5 / 120 - v20A^7 / 5040 + v20A^9 / 362880 := hs
    _ = (5334193 / 5806080 : ℝ) * v20A := by
      rw [v20_A_pow3, v20_A_pow5, v20_A_pow7, v20_A_pow9]
      ring

/-- Rational lower bound for `cos(1/sqrt 2)`. -/
private lemma v20_cosA_lower :
    (88280819 / 116121600 : ℝ) ≤ Real.cos v20A := by
  have hc := v20_cos_lower10 (x := v20A) v20_A_pos.le v20_A_le_one
  calc
    (88280819 / 116121600 : ℝ) =
        1 - v20A^2 / 2 + v20A^4 / 24 - v20A^6 / 720
          + v20A^8 / 40320 - v20A^10 / 3628800 := by
      rw [v20_A_sq, v20_A_pow4, v20_A_pow6, v20_A_pow8, v20_A_pow10]
      norm_num
    _ ≤ Real.cos v20A := hc

private lemma v20_theta_lower :
    (172787593 / 500000000 : ℝ) < v20Theta := by
  unfold v20Theta
  nlinarith [v20_pi_lower]

private lemma v20_theta_upper :
    v20Theta < (345575197 / 1000000000 : ℝ) := by
  unfold v20Theta
  nlinarith [v20_pi_upper]

/-- Rational lower bound for `sin(11*pi/100)`. -/
private lemma v20_sinTheta_lower :
    (3387379 / 10000000 : ℝ) < Real.sin v20Theta := by
  let tL : ℝ := 172787593 / 500000000
  have htL0 : 0 ≤ tL := by norm_num [tL]
  have htL1 : tL ≤ 1 := by norm_num [tL]
  have hTaylor := v20_sin_lower7 (x := tL) htL0 htL1
  have hrat :
      (3387379 / 10000000 : ℝ) <
        tL - tL^3 / 6 + tL^5 / 120 - tL^7 / 5040 := by
    norm_num [tL]
  have hmono : Real.sin tL ≤ Real.sin v20Theta := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have hp := Real.pi_pos
      nlinarith [htL0]
    · unfold v20Theta
      nlinarith [Real.pi_pos]
    · exact v20_theta_lower.le
  exact hrat.trans_le (hTaylor.trans hmono)

/-- Rational lower bound for `cos(11*pi/100)`. -/
private lemma v20_cosTheta_lower :
    (9408807 / 10000000 : ℝ) < Real.cos v20Theta := by
  let tU : ℝ := 345575197 / 1000000000
  have htU0 : 0 ≤ tU := by norm_num [tU]
  have htU1 : tU ≤ 1 := by norm_num [tU]
  have hTaylor := v20_cos_lower10 (x := tU) htU0 htU1
  have hrat :
      (9408807 / 10000000 : ℝ) <
        1 - tU^2 / 2 + tU^4 / 24 - tU^6 / 720
          + tU^8 / 40320 - tU^10 / 3628800 := by
    norm_num [tU]
  have hmono : Real.cos tU ≤ Real.cos v20Theta := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · unfold v20Theta
      positivity
    · nlinarith [v20_pi_lower]
    · exact v20_theta_upper.le
  exact hrat.trans_le (hTaylor.trans hmono)

private lemma v20_B_lower :
    (1398008707 / 500000000 : ℝ) < v20B := by
  unfold v20B
  nlinarith [v20_pi_lower]

private lemma v20_B_upper :
    v20B < (2796017503 / 1000000000 : ℝ) := by
  unfold v20B
  nlinarith [v20_pi_upper]

/-- The all-rational inequality left after replacing every transcendental
quantity by the directed bounds proved above. -/
private lemma v20_rational_margin :
    (171389 / 1000000 : ℝ) *
        (((2796017503 / 1000000000 : ℝ)^2 - 1 / 2) *
          (5334193 / 5806080 : ℝ))
      <
        (1 / 2 : ℝ) * (37043 / 40320 : ℝ) * (9408807 / 10000000 : ℝ)
        + (1398008707 / 500000000 : ℝ) *
          (88280819 / 116121600 : ℝ) * (3387379 / 10000000 : ℝ) := by
  norm_num

/-- Closed-form target for the normalized Montgomery--Taylor kernel. -/
def v20ClosedKernel (x : ℝ) : ℝ :=
  (Real.cos (Real.pi * x)
    - Real.sqrt 2 * Real.pi * x *
        (Real.cos ((Real.sqrt 2)⁻¹) / Real.sin ((Real.sqrt 2)⁻¹)) *
        Real.sin (Real.pi * x)) /
  (1 - 2 * (Real.pi * x)^2)

/-- The integral definition used by v17 agrees with its elementary closed form. -/
theorem v20_limitingk_closed_form
    {x : ℝ}
    (hden : 1 - 2 * (Real.pi * x)^2 ≠ 0) :
    limitingk x = v20ClosedKernel x := by
  sorry

/-- Analytic numerical theorem at the exact point used by v17. -/
theorem v20_kernel_signed_89_100 :
    (171389 / 1000000 : ℝ) < limitingk (89 / 100 : ℝ) := by
  sorry

end HurtadoZeta23
