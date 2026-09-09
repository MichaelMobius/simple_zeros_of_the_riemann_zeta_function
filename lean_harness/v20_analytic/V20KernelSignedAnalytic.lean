import HurtadoZeta23.LimitingKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section

open Filter Finset
open scoped BigOperators

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
  x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)

private def cosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n)! : ℝ)

private lemma sinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (sinTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold sinTerm
  gcongr
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)

private lemma cosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (cosTerm x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold cosTerm
  gcongr
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega : 2 * n ≤ 2 * (n + 1))

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
