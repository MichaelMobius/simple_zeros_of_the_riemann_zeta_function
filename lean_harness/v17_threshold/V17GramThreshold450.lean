import HurtadoZeta23.V17TraceLeSpectralThreshold
import HurtadoZeta23.ConcreteBlockDefect
import HurtadoZeta23.MatrixEnergy
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder
open RHLinalg

namespace HurtadoZeta23

/-- A 450-by-450 matrix whose real diagonal entries are at most one has real
trace at most 450. -/
theorem v17_rtrace_le_450_of_diag_re_le_one
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hdiag : ∀ i : Fin 450, (G i i).re ≤ 1) :
    rtrace G ≤ 450 := by
  unfold rtrace
  change RCLike.re (∑ i : Fin 450, G i i) ≤ 450
  rw [map_sum]
  calc
    (∑ i : Fin 450, (G i i).re) ≤ ∑ _i : Fin 450, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i hi => hdiag i
    _ = 450 := by simp

/-- General finite-safe spectral threshold for a PSD 450-by-450 matrix.

Only the one-sided trace bound is needed. If the spectral defect is below the
off-diagonal Gram energy, then it is below the full Frobenius deviation; the
exact `450/449` scalar threshold applies and is stronger than the finite-safe
`5011/5000` threshold used by the block finisher. -/
theorem v17_psd_gram_threshold_450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (htrace : rtrace G ≤ 450)
    (hDO : gramSpectralDefect G hG < offDiagonalEnergy G) :
    v17FiniteThreshold < gramSpectralDefect G hG := by
  let lam : Fin 450 → ℝ := hG.isHermitian.eigenvalues
  let E : ℝ := frobeniusDeviationSq G
  let D : ℝ := gramSpectralDefect G hG

  have hlam0 : ∀ i : Fin 450, 0 ≤ lam i := by
    intro i
    dsimp [lam]
    exact hG.eigenvalues_nonneg i

  have hsum : ∑ i, lam i ≤ 450 := by
    dsimp [lam]
    rw [← rtrace_eq_sum_eigenvalues hG.isHermitian]
    exact htrace

  have hD : D = ∑ i, psi (lam i) := by
    dsimp [D, lam]
    unfold gramSpectralDefect
    exact (sum_eigenvalues_reindex hG.isHermitian psi).symm

  have hE : E = ∑ i, (lam i - 1) ^ 2 := by
    have hFS := frobeniusSpectralIdentity_proved G hG.isHermitian
    unfold FrobeniusSpectralIdentity spectralDeviationSq at hFS
    dsimp [E, lam]
    exact hFS

  have hOE : offDiagonalEnergy G ≤ E := by
    dsimp [E]
    exact offDiagonalEnergy_le_frobeniusDeviationSq G

  have hDE : D < E := by
    dsimp [D] at hDO
    exact lt_of_lt_of_le hDO hOE

  have hexact : v17Threshold < D :=
    v17_spectral_threshold_fin450_sum_le
      lam hlam0 hsum hD hE hDE

  have hfinite : v17FiniteThreshold < v17Threshold := by
    norm_num [v17FiniteThreshold, v17Threshold]

  exact lt_trans hfinite hexact

/-- Diagonal-bound version of the same threshold. -/
theorem v17_psd_gram_threshold_450_of_diag
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 450, (G i i).re ≤ 1)
    (hDO : gramSpectralDefect G hG < offDiagonalEnergy G) :
    v17FiniteThreshold < gramSpectralDefect G hG := by
  exact v17_psd_gram_threshold_450 G hG
    (v17_rtrace_le_450_of_diag_re_le_one G hdiag) hDO

end HurtadoZeta23
