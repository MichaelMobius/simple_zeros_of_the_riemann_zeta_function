import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

noncomputable section

open Filter Finset Real
open scoped BigOperators Topology

namespace HurtadoZeta23

private def v21SinTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)

private def v21CosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n).factorial : ℝ)

private lemma v21SinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (v21SinTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold v21SinTerm
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

private lemma v21CosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (v21CosTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold v21CosTerm
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
lemma v21_sin_lower7 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x^3 / 6 + x^5 / 120 - x^7 / 5040 ≤ Real.sin x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * v21SinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [v21SinTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (v21SinTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 2
  norm_num [v21SinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Four-term alternating Taylor lower bound for cosine on `[0,1]`. -/
lemma v21_cos_lower6 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x^2 / 2 + x^4 / 24 - x^6 / 720 ≤ Real.cos x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * v21CosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [v21CosTerm, mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (v21CosTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 2
  norm_num [v21CosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Six-term alternating Taylor lower bound for cosine on `[0,1]`. -/
lemma v21_cos_lower10 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x^2 / 2 + x^4 / 24 - x^6 / 720 + x^8 / 40320 - x^10 / 3628800
      ≤ Real.cos x := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * v21CosTerm x i)
        atTop (𝓝 (Real.cos x)) := by
    simpa [v21CosTerm, mul_div_assoc] using (Real.hasSum_cos x).tendsto_sum_nat
  have h := (v21CosTerm_antitone hx0 hx1).alternating_series_le_tendsto ht 3
  norm_num [v21CosTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- Five-term alternating Taylor upper bound for sine on `[0,1]`. -/
lemma v21_sin_upper9 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x^3 / 6 + x^5 / 120 - x^7 / 5040 + x^9 / 362880 := by
  have ht :
      Tendsto
        (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ)^i * v21SinTerm x i)
        atTop (𝓝 (Real.sin x)) := by
    simpa [v21SinTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have h := (v21SinTerm_antitone hx0 hx1).tendsto_le_alternating_series ht 2
  norm_num [v21SinTerm, sum_range_succ, Nat.factorial] at h ⊢
  linarith

end HurtadoZeta23
