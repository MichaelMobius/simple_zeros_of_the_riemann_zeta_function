import HurtadoZeta23.BlockDefect
import HurtadoZeta23.V17StrongBlockScalar
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-- Supporting-line lower bound for `psi` at a point `c ∈ [0,1]`.
This is the scalar Jensen input needed for the `m=450` threshold. -/
theorem v17_psi_tangent_lower
    {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c - 1) ^ 2 + 2 * (c - 1) * (x - c) ≤ psi x := by
  by_cases hx : x ≤ 2
  · rw [psi_eq_sq hx]
    nlinarith [sq_nonneg (x - c)]
  · have hx2 : 2 < x := lt_of_not_ge hx
    rw [psi_eq_linear hx2]
    have h1 : 0 ≤ 2 - c := by linarith
    have h2 : 0 ≤ 2 * x - c - 2 := by linarith
    have hp : 0 ≤ (2 - c) * (2 * x - c - 2) := mul_nonneg h1 h2
    nlinarith

/-- Spectral threshold in purely scalar form, specialised to 450 eigenvalues.
If the `psi` defect is strictly smaller than the centered quadratic energy,
then one eigenvalue is above two; trace 450 plus the tangent bound on the
remaining 449 eigenvalues forces `D > 450/449`. -/
theorem v17_spectral_threshold_fin450
    (lam : Fin 450 → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (hsum : ∑ i, lam i = 450)
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
  have hsum_rest : ∑ i ∈ S, lam i = 449 - a := by
    have h := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h
    dsimp [S, a]
    linarith
  have hrest0 : 0 ≤ ∑ i ∈ S, lam i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hlam0 i
  have ha449 : a ≤ 449 := by
    linarith [hsum_rest, hrest0]

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

  have htangent_eval :
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
        = a ^ 2 / 449 := by
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
      _ = a ^ 2 / 449 := by
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
  have hrest : a ^ 2 / 449 ≤ ∑ i ∈ S, psi (lam i) := by
    rw [← htangent_eval]
    exact htangent
  have hquad : 2 * a - 1 + a ^ 2 / 449 ≤ D := by
    rw [hDsplit, hkpsi]
    linarith
  exact v17_threshold_from_quadratic ha hquad

end HurtadoZeta23
