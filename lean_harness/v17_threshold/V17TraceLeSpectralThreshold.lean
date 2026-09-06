import HurtadoZeta23.V17SpectralThreshold
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-- The exact `450/449` threshold remains valid when the total trace is only
known to be at most 450.  A trace deficit makes the convex lower bound on the
remaining 449 eigenvalues stronger, not weaker. -/
theorem v17_spectral_threshold_fin450_sum_le
    (lam : Fin 450 → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (hsum : ∑ i, lam i ≤ 450)
    {D E : ℝ}
    (hD : D = ∑ i, psi (lam i))
    (hE : E = ∑ i, (lam i - 1) ^ 2)
    (hDE : D < E) :
    v17Threshold < D := by
  have hlarge : ∃ k : Fin 450, 2 < lam k := by
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

  let S : Finset (Fin 450) := Finset.univ.erase k
  have hsplit :
      (∑ i : Fin 450, lam i) = lam k + ∑ i ∈ S, lam i := by
    dsimp [S]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]

  have hsum_rest : ∑ i ∈ S, lam i ≤ 449 - a := by
    dsimp [a]
    linarith

  have hrest0 : 0 ≤ ∑ i ∈ S, lam i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hlam0 i

  have ha449 : a ≤ 449 := by
    linarith

  let c : ℝ := 1 - a / 449
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
    exact v17_psi_tangent_lower hc0 hc1

  have hcard : S.card = 449 := by
    dsimp [S]
    simp

  have htangent_form :
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
        =
      449 * (c - 1) ^ 2 +
        2 * (c - 1) * ((∑ i ∈ S, lam i) - 449 * c) := by
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
      _ = 449 * (c - 1) ^ 2 +
              2 * (c - 1) * ((∑ i ∈ S, lam i) - 449 * c) := by
            rw [hcard]
            norm_num

  have hdiff : (∑ i ∈ S, lam i) - 449 * c ≤ 0 := by
    dsimp [c]
    nlinarith

  have hcneg : c - 1 ≤ 0 := by linarith
  have hmul :
      0 ≤ (c - 1) * ((∑ i ∈ S, lam i) - 449 * c) :=
    mul_nonneg_of_nonpos_of_nonpos hcneg hdiff

  have hbase : 449 * (c - 1) ^ 2 = a ^ 2 / 449 := by
    dsimp [c]
    norm_num
    ring

  have hrest : a ^ 2 / 449 ≤ ∑ i ∈ S, psi (lam i) := by
    have htanlower :
        a ^ 2 / 449 ≤
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

  have hquad : 2 * a - 1 + a ^ 2 / 449 ≤ D := by
    rw [hDsplit, hkpsi]
    linarith

  exact v17_threshold_from_quadratic ha hquad

end HurtadoZeta23
