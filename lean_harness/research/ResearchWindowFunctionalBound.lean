import HurtadoZeta23.ResearchNinePointHybrid
import HurtadoZeta23.ResearchWindowPositivity
import Zeta23.ThmD.Functional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section

open Filter Finset Real
open scoped BigOperators Topology

namespace HurtadoZeta23

/-!
# Closed-form functional bound for the pinned nine-point window

This module proves the high-precision transcendental/rational inequality for

  H_MT - delta / (2 sin(1/sqrt(2))^2),

where the perturbation correction `delta` is the exact expression obtained
after the cosine-mode orthogonality and base-mode cross cancellation.  The
separate moment bridge will identify this closed expression with the actual
window functional.
-/

private def research9FSinTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)

private def research9FCosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n).factorial : ℝ)

private lemma research9FSinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (research9FSinTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold research9FSinTerm
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

private lemma research9FCosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (research9FCosTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold research9FCosTerm
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

/-- Fifteenth-degree alternating lower bound for sine on `[0,1]`. -/
theorem research9_sin_lower15 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x^3 / 6 + x^5 / 120 - x^7 / 5040 + x^9 / 362880
      - x^11 / 39916800 + x^13 / 6227020800 - x^15 / 1307674368000
      ≤ Real.sin x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * research9FSinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [research9FSinTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (research9FSinTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 4
  norm_num [research9FSinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Sixteenth-degree alternating upper bound for cosine on `[0,1]`. -/
theorem research9_cos_upper16 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cos x ≤
      1 - x^2 / 2 + x^4 / 24 - x^6 / 720 + x^8 / 40320
        - x^10 / 3628800 + x^12 / 479001600 - x^14 / 87178291200
        + x^16 / 20922789888000 := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * research9FCosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [research9FCosTerm, mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (research9FCosTerm_antitone hx0 hx1).tendsto_le_alternating_series ht 4
  norm_num [research9FCosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

def research9FunctionalA : ℝ := (Real.sqrt 2)⁻¹

def research9FunctionalAlo : ℝ := 7071067811865475 / 10000000000000000

def research9FunctionalAhi : ℝ := 7071067811865476 / 10000000000000000

private lemma research9FunctionalA_pos : 0 < research9FunctionalA := by
  unfold research9FunctionalA
  positivity

private lemma research9FunctionalA_sq : research9FunctionalA ^ 2 = (1 / 2 : ℝ) := by
  unfold research9FunctionalA
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma research9FunctionalA_lower :
    research9FunctionalAlo < research9FunctionalA := by
  by_contra h
  have hle : research9FunctionalA ≤ research9FunctionalAlo := le_of_not_gt h
  have hprod :
      0 ≤ (research9FunctionalAlo - research9FunctionalA) *
        (research9FunctionalAlo + research9FunctionalA) := by
    apply mul_nonneg
    · linarith
    · nlinarith [research9FunctionalA_pos.le]
  norm_num [research9FunctionalAlo] at hprod
  nlinarith [research9FunctionalA_sq]

private lemma research9FunctionalA_upper :
    research9FunctionalA < research9FunctionalAhi := by
  by_contra h
  have hle : research9FunctionalAhi ≤ research9FunctionalA := le_of_not_gt h
  have hprod :
      0 ≤ (research9FunctionalA - research9FunctionalAhi) *
        (research9FunctionalA + research9FunctionalAhi) := by
    apply mul_nonneg
    · linarith
    · have hAhi0 : 0 <= research9FunctionalAhi := by
        norm_num [research9FunctionalAhi]
      exact add_nonneg research9FunctionalA_pos.le hAhi0
  norm_num [research9FunctionalAhi] at hprod
  nlinarith [research9FunctionalA_sq]

/-- Exact rational Taylor lower surrogate for `sin(1/sqrt(2))`. -/
def research9FunctionalSinLower : ℝ :=
  research9FunctionalAlo - research9FunctionalAlo^3 / 6
    + research9FunctionalAlo^5 / 120 - research9FunctionalAlo^7 / 5040
    + research9FunctionalAlo^9 / 362880 - research9FunctionalAlo^11 / 39916800
    + research9FunctionalAlo^13 / 6227020800
    - research9FunctionalAlo^15 / 1307674368000

/-- Exact rational Taylor upper surrogate for `cos(1/sqrt(2))`. -/
def research9FunctionalCosUpper : ℝ :=
  1 - research9FunctionalAlo^2 / 2 + research9FunctionalAlo^4 / 24
    - research9FunctionalAlo^6 / 720 + research9FunctionalAlo^8 / 40320
    - research9FunctionalAlo^10 / 3628800
    + research9FunctionalAlo^12 / 479001600
    - research9FunctionalAlo^14 / 87178291200
    + research9FunctionalAlo^16 / 20922789888000

private lemma research9FunctionalSinLower_pos : 0 < research9FunctionalSinLower := by
  norm_num [research9FunctionalSinLower, research9FunctionalAlo]

private lemma research9FunctionalSin_lower :
    research9FunctionalSinLower ≤ Real.sin research9FunctionalA := by
  have ha0 : 0 ≤ research9FunctionalAlo := by norm_num [research9FunctionalAlo]
  have ha1 : research9FunctionalAlo ≤ 1 := by norm_num [research9FunctionalAlo]
  have ht := research9_sin_lower15 (x := research9FunctionalAlo) ha0 ha1
  have hA_lt_one : research9FunctionalA < 1 := by
    exact lt_trans research9FunctionalA_upper (by
      norm_num [research9FunctionalAhi])
  have hA_le_pi_div_two : research9FunctionalA <= Real.pi / 2 := by
    nlinarith [Real.pi_gt_three, hA_lt_one]
  have hmono : Real.sin research9FunctionalAlo ≤ Real.sin research9FunctionalA := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · exact hA_le_pi_div_two
    · exact research9FunctionalA_lower.le
  exact ht.trans hmono

private lemma research9FunctionalCos_upper :
    Real.cos research9FunctionalA ≤ research9FunctionalCosUpper := by
  have ha0 : 0 ≤ research9FunctionalAlo := by norm_num [research9FunctionalAlo]
  have ha1 : research9FunctionalAlo ≤ 1 := by norm_num [research9FunctionalAlo]
  have ht := research9_cos_upper16 (x := research9FunctionalAlo) ha0 ha1
  have hA_lt_one : research9FunctionalA < 1 := by
    exact lt_trans research9FunctionalA_upper (by
      norm_num [research9FunctionalAhi])
  have hA_le_pi : research9FunctionalA <= Real.pi := by
    nlinarith [Real.pi_gt_three, hA_lt_one]
  have hmono : Real.cos research9FunctionalA ≤ Real.cos research9FunctionalAlo := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact ha0
    · exact hA_le_pi
    · exact research9FunctionalA_lower.le
  exact hmono.trans ht

def research9HMTLower : ℝ := 6725007036794 / 10000000000000

/-- High-precision exact-rational lower bound for the Montgomery--Taylor
baseline `HD 1`. -/
theorem research9_HMT_gt_lower :
    research9HMTLower < Zeta23.ThmD.HD 1 := by
  have hsinpos : 0 < Real.sin research9FunctionalA := by
    have h := Zeta23.ThmD.sin_theta_pos (lam := (1 : ℝ)) one_pos le_rfl
    rw [Zeta23.ThmD.theta_one] at h
    exact h
  have hcospos : 0 < Real.cos research9FunctionalA := by
    have h := Zeta23.ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) le_rfl
    rw [Zeta23.ThmD.theta_one] at h
    exact h
  have hprod1 :
      research9FunctionalA * Real.cos research9FunctionalA ≤
        research9FunctionalAhi * Real.cos research9FunctionalA :=
    mul_le_mul_of_nonneg_right research9FunctionalA_upper.le hcospos.le
  have hprod2 :
      research9FunctionalAhi * Real.cos research9FunctionalA ≤
        research9FunctionalAhi * research9FunctionalCosUpper :=
    mul_le_mul_of_nonneg_left research9FunctionalCos_upper
      (by norm_num [research9FunctionalAhi])
  have hprod := hprod1.trans hprod2
  have hrat :
      research9FunctionalAhi * research9FunctionalCosUpper <
        (3 / 2 - research9HMTLower) * research9FunctionalSinLower := by
    norm_num [research9FunctionalAhi, research9FunctionalCosUpper,
      research9FunctionalSinLower, research9FunctionalAlo, research9HMTLower]
  have hR : 0 ≤ 3 / 2 - research9HMTLower := by
    norm_num [research9HMTLower]
  have hright :
      (3 / 2 - research9HMTLower) * research9FunctionalSinLower ≤
        (3 / 2 - research9HMTLower) * Real.sin research9FunctionalA :=
    mul_le_mul_of_nonneg_left research9FunctionalSin_lower hR
  have hcross :
      research9FunctionalA * Real.cos research9FunctionalA <
        (3 / 2 - research9HMTLower) * Real.sin research9FunctionalA :=
    hprod.trans_lt (hrat.trans_le hright)
  have hratio :
      research9FunctionalA *
          (Real.cos research9FunctionalA / Real.sin research9FunctionalA) <
        3 / 2 - research9HMTLower := by
    rw [show research9FunctionalA *
        (Real.cos research9FunctionalA / Real.sin research9FunctionalA) =
        (research9FunctionalA * Real.cos research9FunctionalA) /
          Real.sin research9FunctionalA by ring]
    exact (div_lt_iff₀ hsinpos).2 hcross
  rw [Zeta23.ThmD.HD_one]
  change research9HMTLower <
    3 / 2 - research9FunctionalA *
      (Real.cos research9FunctionalA / Real.sin research9FunctionalA)
  linarith

/-- Sum of squares of the six perturbation coefficients. -/
def research9FunctionalS0 : ℝ :=
  75016585491221 / 1000000000000000000

/-- `sum d_n^2/n^2` for the six integer-frequency perturbations. -/
def research9FunctionalS2 : ℝ :=
  23268362407797749 / 900000000000000000000

/-- Audit that `S0` is exactly the coefficient-square sum. -/
theorem research9_functional_S0_exact :
    (3322500 / 1000000000 : ℝ)^2 +
      (7609135 / 1000000000 : ℝ)^2 +
      (1190194 / 1000000000 : ℝ)^2 +
      (731476 / 1000000000 : ℝ)^2 +
      (1680572 / 1000000000 : ℝ)^2 +
      (1141360 / 1000000000 : ℝ)^2 = research9FunctionalS0 := by
  norm_num [research9FunctionalS0]

/-- Audit that `S2` is exactly the weighted coefficient-square sum. -/
theorem research9_functional_S2_exact :
    (3322500 / 1000000000 : ℝ)^2 / 1^2 +
      (7609135 / 1000000000 : ℝ)^2 / 2^2 +
      (1190194 / 1000000000 : ℝ)^2 / 3^2 +
      (731476 / 1000000000 : ℝ)^2 / 4^2 +
      (1680572 / 1000000000 : ℝ)^2 / 5^2 +
      (1141360 / 1000000000 : ℝ)^2 / 6^2 = research9FunctionalS2 := by
  norm_num [research9FunctionalS2]

/-- Exact closed perturbation correction after orthogonality/cancellation. -/
def research9FunctionalDelta : ℝ :=
  research9FunctionalS0 / 2 - research9FunctionalS2 / (4 * Real.pi ^ 2)

def research9FunctionalPiUpper : ℝ :=
  314159265358979323847 / 100000000000000000000

def research9FunctionalDeltaUpper : ℝ :=
  research9FunctionalS0 / 2 -
    research9FunctionalS2 / (4 * research9FunctionalPiUpper ^ 2)

private lemma research9Functional_pi_lt_upper :
    Real.pi < research9FunctionalPiUpper := by
  unfold research9FunctionalPiUpper
  nlinarith [Real.pi_lt_d20]

private lemma research9Functional_delta_lt_upper :
    research9FunctionalDelta < research9FunctionalDeltaUpper := by
  have hp := research9Functional_pi_lt_upper
  have hpU : 0 < research9FunctionalPiUpper := by
    norm_num [research9FunctionalPiUpper]
  have hsquares : Real.pi ^ 2 < research9FunctionalPiUpper ^ 2 := by
    have hprod :
        0 < (research9FunctionalPiUpper - Real.pi) *
          (research9FunctionalPiUpper + Real.pi) := by
      apply mul_pos
      · exact sub_pos.mpr hp
      · nlinarith [Real.pi_pos, hpU]
    nlinarith
  have hden : 4 * Real.pi ^ 2 < 4 * research9FunctionalPiUpper ^ 2 := by
    nlinarith
  have hS2 : 0 < research9FunctionalS2 := by
    norm_num [research9FunctionalS2]
  have hfrac :
      research9FunctionalS2 / (4 * research9FunctionalPiUpper ^ 2) <
        research9FunctionalS2 / (4 * Real.pi ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 4 * research9FunctionalPiUpper ^ 2)
      (by positivity : 0 < 4 * Real.pi ^ 2)).2
    exact mul_lt_mul_of_pos_left hden hS2
  unfold research9FunctionalDelta research9FunctionalDeltaUpper
  linarith

/-- The exact correction subtracted from the MT baseline. -/
def research9FunctionalCorrection : ℝ :=
  research9FunctionalDelta /
    (2 * Real.sin research9FunctionalA ^ 2)

def research9FunctionalCorrectionUpper : ℝ :=
  43662264868 / 1000000000000000

/-- High-precision exact-rational upper bound for the perturbation correction. -/
theorem research9_functional_correction_lt_upper :
    research9FunctionalCorrection < research9FunctionalCorrectionUpper := by
  have hdelta := research9Functional_delta_lt_upper
  have hsL := research9FunctionalSin_lower
  have hsLpos := research9FunctionalSinLower_pos
  have hsinpos : 0 < Real.sin research9FunctionalA := by
    have h := Zeta23.ThmD.sin_theta_pos (lam := (1 : ℝ)) one_pos le_rfl
    rw [Zeta23.ThmD.theta_one] at h
    exact h
  have hsq : research9FunctionalSinLower ^ 2 ≤
      Real.sin research9FunctionalA ^ 2 :=
    pow_le_pow_left₀ hsLpos.le hsL 2
  have hden :
      2 * research9FunctionalSinLower ^ 2 ≤
        2 * Real.sin research9FunctionalA ^ 2 := by nlinarith
  have hrat :
      research9FunctionalDeltaUpper <
        research9FunctionalCorrectionUpper *
          (2 * research9FunctionalSinLower ^ 2) := by
    norm_num [research9FunctionalDeltaUpper, research9FunctionalS0,
      research9FunctionalS2, research9FunctionalPiUpper,
      research9FunctionalCorrectionUpper, research9FunctionalSinLower,
      research9FunctionalAlo]
  have hCup : 0 ≤ research9FunctionalCorrectionUpper := by
    norm_num [research9FunctionalCorrectionUpper]
  have hchain :
      research9FunctionalDelta <
        research9FunctionalCorrectionUpper *
          (2 * Real.sin research9FunctionalA ^ 2) :=
    hdelta.trans (hrat.trans_le (mul_le_mul_of_nonneg_left hden hCup))
  unfold research9FunctionalCorrection
  exact (div_lt_iff₀ (by positivity : 0 < 2 * Real.sin research9FunctionalA ^ 2)).2 hchain

/-- The closed functional value predicted by the exact mode-cancellation
identity. -/
def research9WindowFunctionalClosed : ℝ :=
  Zeta23.ThmD.HD 1 - research9FunctionalCorrection

/-- Exact rational margin left after the two convenient high-precision bounds. -/
theorem research9_functional_rational_margin :
    research9HMTLower - research9FunctionalCorrectionUpper - research9Hcert
      = 3633 / 250000000000000 := by
  norm_num [research9HMTLower, research9FunctionalCorrectionUpper, research9Hcert]

/-- The closed-form pinned-window functional strictly exceeds the certified
baseline used by the nine-point/global assembly. -/
theorem research9_window_functional_closed_gt_Hcert :
    research9Hcert < research9WindowFunctionalClosed := by
  have hb := research9_HMT_gt_lower
  have hc := research9_functional_correction_lt_upper
  have hm := research9_functional_rational_margin
  unfold research9WindowFunctionalClosed
  nlinarith

end HurtadoZeta23
