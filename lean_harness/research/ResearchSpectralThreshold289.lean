import HurtadoZeta23.BlockDefect
import HurtadoZeta23.ResearchNinePointHybrid
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Research-only spectral threshold for the `m = 289` block

This is the `Fin 289` analogue of the already established v17 scalar spectral
threshold.  It is kept on the research branch and depends only on the project
spectral defect function `psi` plus exact finite-sum algebra.
-/

/-- Supporting-line lower bound for `psi` at a point `c ∈ [0,1]`.
The proof is dimension-free and is repeated here so this research module does
not depend on the hard-coded `Fin 450` v17 theorem. -/
theorem research9_psi_tangent_lower
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

/-- Once the spectral argument supplies the standard lower bound
`2*a - 1 + a^2/288` with `a > 1`, the ideal `289/288` threshold follows. -/
theorem research9_threshold_from_quadratic
    {D a : ℝ}
    (ha : 1 < a)
    (hD : 2 * a - 1 + a ^ 2 / 288 ≤ D) :
    research9Threshold < D := by
  have hs : 0 ≤ (a - 1) ^ 2 := sq_nonneg (a - 1)
  norm_num [research9Threshold] at hD ⊢
  nlinarith

/-- Spectral threshold in scalar form for exactly 289 nonnegative eigenvalues
of trace 289.  If the `psi` defect is strictly smaller than the centered
quadratic energy, at least one eigenvalue lies above two; the tangent lower
bound on the other 288 eigenvalues then forces `D > 289/288`. -/
theorem research9_spectral_threshold_fin289
    (lam : Fin 289 → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (hsum : ∑ i, lam i = 289)
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
  have hsum_rest : ∑ i ∈ S, lam i = 288 - a := by
    have h := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h
    dsimp [S, a]
    linarith
  have hrest0 : 0 ≤ ∑ i ∈ S, lam i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hlam0 i
  have ha288 : a ≤ 288 := by
    linarith [hsum_rest, hrest0]

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

  have htangent_eval :
      (∑ i ∈ S,
          ((c - 1) ^ 2 + 2 * (c - 1) * (lam i - c)))
        = a ^ 2 / 288 := by
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
      _ = a ^ 2 / 288 := by
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
  have hrest : a ^ 2 / 288 ≤ ∑ i ∈ S, psi (lam i) := by
    rw [← htangent_eval]
    exact htangent
  have hquad : 2 * a - 1 + a ^ 2 / 288 ≤ D := by
    rw [hDsplit, hkpsi]
    linarith
  exact research9_threshold_from_quadratic ha hquad

end HurtadoZeta23
