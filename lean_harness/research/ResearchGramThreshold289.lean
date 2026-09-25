import HurtadoZeta23.ResearchTraceLeSpectralThreshold289
import HurtadoZeta23.V17FrobeniusBridge
import HurtadoZeta23.MatrixEnergy
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder
open RHLinalg

namespace HurtadoZeta23

/-!
# PSD Gram threshold for the research `m = 289` block

This is the matrix-facing bridge needed by the research strong-block chain.  It
uses the exact `289/288` scalar threshold proved independently in the research
namespace and only generic project identities for PSD matrices and Frobenius
energy.
-/

/-- A 289-by-289 matrix whose real diagonal entries are at most one has real
trace at most 289. -/
theorem research9_rtrace_le_289_of_diag_re_le_one
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1) :
    rtrace G ≤ 289 := by
  unfold rtrace
  change RCLike.re (∑ i : Fin 289, G i i) ≤ 289
  rw [map_sum]
  calc
    (∑ i : Fin 289, (G i i).re) ≤ ∑ _i : Fin 289, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i hi => hdiag i
    _ = 289 := by simp

/-- Exact research spectral threshold for a PSD 289-by-289 Gram matrix under a
one-sided trace bound. -/
theorem research9_psd_gram_threshold_289
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (htrace : rtrace G ≤ 289)
    (hDO : gramSpectralDefect G hG < offDiagonalEnergy G) :
    research9Threshold < gramSpectralDefect G hG := by
  let lam : Fin 289 → ℝ := hG.isHermitian.eigenvalues
  let E : ℝ := frobeniusDeviationSq G
  let D : ℝ := gramSpectralDefect G hG

  have hlam0 : ∀ i : Fin 289, 0 ≤ lam i := by
    intro i
    dsimp [lam]
    exact hG.eigenvalues_nonneg i

  have hsum : ∑ i, lam i ≤ 289 := by
    dsimp [lam]
    rw [← rtrace_eq_sum_eigenvalues hG.isHermitian]
    exact htrace

  have hD : D = ∑ i, psi (lam i) := by
    dsimp [D, lam]
    unfold gramSpectralDefect
    exact (sum_eigenvalues_reindex hG.isHermitian psi).symm

  have hE : E = ∑ i, (lam i - 1) ^ 2 := by
    have hFS := v17_frobeniusSpectralIdentity_proved G hG.isHermitian
    unfold FrobeniusSpectralIdentity spectralDeviationSq at hFS
    dsimp [E, lam]
    exact hFS

  have hOE : offDiagonalEnergy G ≤ E := by
    dsimp [E]
    exact offDiagonalEnergy_le_frobeniusDeviationSq G

  have hDE : D < E := lt_of_lt_of_le hDO hOE

  exact research9_spectral_threshold_fin289_sum_le
    lam hlam0 hsum hD hE hDE

/-- Diagonal-bound version of the same exact threshold. -/
theorem research9_psd_gram_threshold_289_of_diag
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1)
    (hDO : gramSpectralDefect G hG < offDiagonalEnergy G) :
    research9Threshold < gramSpectralDefect G hG := by
  exact research9_psd_gram_threshold_289 G hG
    (research9_rtrace_le_289_of_diag_re_le_one G hdiag) hDO

end HurtadoZeta23
