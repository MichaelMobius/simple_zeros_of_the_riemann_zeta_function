import HurtadoZeta23.ConcreteBlockDefect
import HurtadoZeta23.V17SpectralThreshold
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- A PSD `450 × 450` Gram matrix with diagonal one satisfies the v17
spectral threshold directly at the level of the actual finite Gram matrix.

This removes the need to transfer the spectral defect from a limiting kernel
matrix to the finite Gram matrix: if the defect is smaller than the actual
off-diagonal energy, the scalar `Fin 450` theorem forces
`D > 450/449`.
-/
theorem v17_matrix_spectral_threshold_fin450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i = 1)
    (hsmall : gramSpectralDefect G hG < offDiagonalEnergy G) :
    v17Threshold < gramSpectralDefect G hG := by
  let lam : Fin 450 → ℝ := hG.isHermitian.eigenvalues

  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    dsimp [lam]
    exact hG.eigenvalues_nonneg i

  have hsum : ∑ i : Fin 450, lam i = 450 := by
    dsimp [lam]
    rw [← RHLinalg.rtrace_eq_sum_eigenvalues hG.isHermitian]
    unfold RHLinalg.rtrace Matrix.trace
    simp [hdiag]

  have hD :
      gramSpectralDefect G hG = ∑ i : Fin 450, psi (lam i) := by
    unfold gramSpectralDefect
    dsimp [lam]
    exact (RHLinalg.sum_eigenvalues_reindex hG.isHermitian psi).symm

  have hdiag0 : diagonalDeviationSq G = 0 := by
    unfold diagonalDeviationSq
    apply Finset.sum_eq_zero
    intro i hi
    rw [hdiag i]
    norm_num

  have hFS := frobeniusSpectralIdentity_proved G hG.isHermitian
  have hE :
      offDiagonalEnergy G = ∑ i : Fin 450, (lam i - 1) ^ 2 := by
    unfold FrobeniusSpectralIdentity spectralDeviationSq at hFS
    rw [frobeniusDeviationSq_eq_diag_add_offdiag, hdiag0, zero_add] at hFS
    dsimp [lam]
    exact hFS

  exact v17_spectral_threshold_fin450
    lam hlam0 hsum hD hE hsmall

end HurtadoZeta23
