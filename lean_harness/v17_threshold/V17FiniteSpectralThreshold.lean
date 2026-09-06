import HurtadoZeta23.V17SpectralThreshold
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-- Robust scalar threshold for a finite 450-point Gram spectrum.

The finite Gram trace is allowed to differ from 450 by at most `9/2000`.
If the `psi` defect is strictly below the centered quadratic spectral energy,
then the defect is still strictly above `5011/5000`.  This is the amount
needed by the finite-error strong-block contradiction. -/
theorem v17_spectral_threshold_fin450_trace_error
    (lam : Fin 450 → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (htrace : |(∑ i, lam i) - 450| ≤ 9 / 2000)
    {D E : ℝ}
    (hD : D = ∑ i, psi (lam i))
    (hE : E = ∑ i, (lam i - 1) ^ 2)
    (hDE : D < E) :
    v17FiniteThreshold < D := by
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

  let tau : ℝ := (∑ i, lam i) - 450
  have htau : tau ≤ 9 / 2000 := by
    have hle : tau ≤ |tau| := le_abs_self tau
    dsimp [tau]
    linarith

  let S : Finset (Fin 450) := Finset.univ.erase k
  have hsum_rest : ∑ i ∈ S, lam i = 449 + tau - a := by
    have hsplit :
        (∑ i : Fin 450, lam i) = lam k + ∑ i ∈ S, lam i := by
      dsimp [S]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    dsimp [tau, a]
    linarith

  have hrest0 : 0 ≤ ∑ i ∈ S, lam i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hlam0 i

  have htaua : tau < a := by
    have hnum : (9 : ℝ) / 2000 < 1 := by norm_num
    linarith

  let c : ℝ := 1 - (a - tau) / 449
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith [hsum_rest, hrest0]
  have hc1 : c ≤ 1 := by
    dsimp [c]
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

  have htangent_eval :
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
        = (a - tau) ^ 2 / 449 := by
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
      _ = (a - tau) ^ 2 / 449 := by
            rw [hcard, hsum_rest]
            dsimp [c]
            norm_num
            ring

  have hDsplit :
      D = psi (lam k) + ∑ i ∈ S, psi (lam i) := by
    rw [hD]
    dsimp [S]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]

  have hkpsi : psi (lam k) = 2 * a - 1 := by
    rw [psi_eq_linear hk]
    dsimp [a]
    ring

  have hrest : (a - tau) ^ 2 / 449 ≤ ∑ i ∈ S, psi (lam i) := by
    rw [← htangent_eval]
    exact htangent

  have hquad : 2 * a - 1 + (a - tau) ^ 2 / 449 ≤ D := by
    rw [hDsplit, hkpsi]
    linarith

  have hgap : (1991 : ℝ) / 2000 < a - tau := by
    linarith
  have hplus : 0 ≤ (1991 : ℝ) / 2000 + (a - tau) := by
    linarith
  have hsq : ((1991 : ℝ) / 2000) ^ 2 < (a - tau) ^ 2 := by
    nlinarith

  have hbase :
      v17FiniteThreshold < 1 + (((1991 : ℝ) / 2000) ^ 2) / 449 := by
    norm_num [v17FiniteThreshold]

  nlinarith

end HurtadoZeta23
