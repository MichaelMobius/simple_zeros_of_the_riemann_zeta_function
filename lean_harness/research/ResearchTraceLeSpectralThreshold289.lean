import HurtadoZeta23.ResearchSpectralThreshold289
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Trace-at-most spectral threshold for the research `m = 289` block

A trace deficit only strengthens the tangent lower bound on the remaining 288
eigenvalues, so the exact ideal threshold `289/288` remains valid under the
finite-safe hypothesis `sum lam ≤ 289`.
-/

/-- The exact `289/288` threshold remains valid when the total trace is only
known to be at most 289. -/
theorem research9_spectral_threshold_fin289_sum_le
    (lam : Fin 289 → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (hsum : ∑ i, lam i ≤ 289)
    {D E : ℝ}
    (hD : D = ∑ i, psi (lam i))
    (hE : E = ∑ i, (lam i - 1) ^ 2)
    (hDE : D < E) :
    research9Threshold < D := by
  have hlarge : ∃ k : Fin 289, 2 < lam k := by
    by_contra hn
    push_neg at hn
    have hEq : D = E := by
      rw [hD, hE]
      apply Finset.sum_congr rfl
      intro i hi
      exact psi_eq_sq (hn i)
    linarith
  obtain ⟨k, hk⟩ := hlarge

  let a : ℝ := lam k - 1
  have ha : 1 < a := by
    dsimp [a]
    linarith

  let S : Finset (Fin 289) := Finset.univ.erase k
  have hsplit :
      (∑ i : Fin 289, lam i) = lam k + ∑ i ∈ S, lam i := by
    dsimp [S]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]

  have hsum_rest : ∑ i ∈ S, lam i ≤ 288 - a := by
    dsimp [a]
    linarith

  have hrest0 : 0 ≤ ∑ i ∈ S, lam i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hlam0 i

  have ha288 : a ≤ 288 := by
    linarith

  let c : ℝ := 1 - a / 288
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have ha0 : 0 ≤ a := le_of_lt (lt_trans (by norm_num) ha)
    nlinarith

  have htangent :
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
        ≤ ∑ i ∈ S, psi (lam i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact research9_psi_tangent_lower hc0 hc1

  have hcard : S.card = 288 := by
    dsimp [S]
    simp

  have htangent_form :
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
        =
      288 * (c - 1) ^ 2 +
        2 * (c - 1) * ((∑ i ∈ S, lam i) - 288 * c) := by
    calc
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
          = (∑ i ∈ S, (c - 1) ^ 2)
              + ∑ i ∈ S, 2 * (c - 1) * (lam i - c) := by
                rw [Finset.sum_add_distrib]
      _ = (S.card : ℝ) * (c - 1) ^ 2
              + 2 * (c - 1) * (∑ i ∈ S, (lam i - c)) := by
            congr 1
            · simp
            · rw [Finset.mul_sum]
      _ = (S.card : ℝ) * (c - 1) ^ 2
              + 2 * (c - 1) *
                  ((∑ i ∈ S, lam i) - (S.card : ℝ) * c) := by
            congr 1
            rw [Finset.sum_sub_distrib]
            simp
      _ = 288 * (c - 1) ^ 2 +
              2 * (c - 1) * ((∑ i ∈ S, lam i) - 288 * c) := by
            rw [hcard]
            norm_num

  have hdiff : (∑ i ∈ S, lam i) - 288 * c ≤ 0 := by
    dsimp [c]
    nlinarith

  have hcneg : c - 1 ≤ 0 := by linarith
  have hmul :
      0 ≤ (c - 1) * ((∑ i ∈ S, lam i) - 288 * c) :=
    mul_nonneg_of_nonpos_of_nonpos hcneg hdiff

  have hbase : 288 * (c - 1) ^ 2 = a ^ 2 / 288 := by
    dsimp [c]
    norm_num
    ring

  have hrest : a ^ 2 / 288 ≤ ∑ i ∈ S, psi (lam i) := by
    have htanlower :
        a ^ 2 / 288 ≤
          ∑ i ∈ S,
            ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)) := by
      rw [htangent_form, hbase]
      nlinarith
    exact le_trans htanlower htangent

  have hDsplit :
      D = psi (lam k) + ∑ i ∈ S, psi (lam i) := by
    rw [hD]
    dsimp [S]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]

  have hkpsi : psi (lam k) = 2 * a - 1 := by
    rw [psi_eq_linear hk]
    dsimp [a]
    ring

  have hquad : 2 * a - 1 + a ^ 2 / 288 ≤ D := by
    rw [hDsplit, hkpsi]
    linarith

  exact research9_threshold_from_quadratic ha hquad

end HurtadoZeta23
