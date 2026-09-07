import HurtadoZeta23.V17StrongBlock450
import HurtadoZeta23.V17AdjacentBand450
import HurtadoZeta23.V17MatrixEnergy450
import HurtadoZeta23.V17GramThreshold450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Matrix wrapper for the abstract v17 strong block

This layer contains all finite linear-algebra structure and nothing analytic.
It converts a PSD 450-by-450 Gram matrix into the two interfaces required by
`v17_strong_block_450_of_interfaces`:

* the complete adjacent band is at most the spectral defect;
* the natural pair energy is exactly the directed off-diagonal energy.

The one-sided diagonal bound also supplies the finite spectral threshold.
-/

theorem v17_strong_block_450_of_matrix_interfaces
    (y : ℕ → ℝ)
    (w : ℕ → ℕ → ℝ)
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i, (G i i).re ≤ 1)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert : SevenPointCertificate w y 450)
    (hscalar : ∀ q < 449,
      v17t * beta * v17g0 ≤
        w q (q + 1) +
          v17t * beta * (y (q + 1) - y q))
    (hpoint : ∀ a b, a < 450 → b < 450 →
      w a b - 2 * eps ≤ v17MatrixNormSqNat450 G a b) :
    v17A - 404100 * eps ≤
      gramSpectralDefect G hG + v17LiteralBlockPressure 450 y := by
  let D : ℝ := gramSpectralDefect G hG
  let O : ℝ := offDiagonalEnergy G

  have hsq :
      v17MatrixNormSqNat450 G = v17MatchingNormSqNat450 G := by
    funext a b
    rfl

  have hband :
      pairBandEnergy 450 0 (v17MatrixNormSqNat450 G) ≤ D := by
    rw [hsq]
    dsimp [D]
    exact v17_adjacent_matrix_band_le_defect_450 G hG hdiag

  have hcomm : ∀ i j : Fin 450,
      ‖G i j‖ ^ 2 = ‖G j i‖ ^ 2 := by
    intro i j
    calc
      ‖G i j‖ ^ 2 = ‖star (G j i)‖ ^ 2 := by
        rw [(hG.isHermitian.apply i j).symm]
      _ = ‖G j i‖ ^ 2 := by simp

  have hglobal :
      globalPairEnergyNat 450 (v17MatrixNormSqNat450 G) = O := by
    dsimp [O]
    exact
      v17_globalPairEnergyNat_matrixNormSq450_eq_offDiagonalEnergy G hcomm

  have hthreshold : D < O → v17FiniteThreshold < D := by
    intro hDO
    dsimp [D, O] at hDO ⊢
    exact v17_psd_gram_threshold_450_of_diag G hG hdiag hDO

  exact
    v17_strong_block_450_of_interfaces
      y w (v17MatrixNormSqNat450 G)
      D O eps heps hw hcert hscalar hpoint hband hglobal hthreshold

end HurtadoZeta23
