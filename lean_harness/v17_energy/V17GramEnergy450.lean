import HurtadoZeta23.V17MatrixEnergy450
import HurtadoZeta23.V17AnalyticBridge450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Concrete v17 Gram-energy identity

The pure finite matrix reindexing now lives in `V17MatrixEnergy450`.  This
module contains only the specialization to the actual 450-point principal Gram
block and the analytic kernel-to-Gram lower bound.
-/

/-- Squared entry norms of the actual v17 principal Gram block are symmetric,
as a direct consequence of Hermitianity. -/
theorem v17Gram450_norm_sq_comm
    (T : ℝ)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (i j : Fin 450) :
    ‖v17Gram450 T s hs i j‖ ^ 2
      = ‖v17Gram450 T s hs j i‖ ^ 2 := by
  have hPSD : (v17Gram450 T s hs).PosSemidef := by
    unfold v17Gram450
    exact
      principal_submatrix_posSemidef
        (articleGlobalSimpleGram T)
        (articleGlobalSimpleGram_posSemidef T)
        (v17SimpleColumn450 T s hs)
  have hHerm : (v17Gram450 T s hs).IsHermitian := hPSD.isHermitian
  calc
    ‖v17Gram450 T s hs i j‖ ^ 2
        = ‖star (v17Gram450 T s hs j i)‖ ^ 2 := by
            rw [(hHerm.apply i j).symm]
    _ = ‖v17Gram450 T s hs j i‖ ^ 2 := by simp

/-- Exact structural identity for the actual 450-point principal Gram block. -/
theorem v17_globalPairEnergyNat_Gram450_eq_offDiagonalEnergy
    (T : ℝ)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    globalPairEnergyNat 450
        (v17MatrixNormSqNat450 (v17Gram450 T s hs))
      =
    offDiagonalEnergy (v17Gram450 T s hs) := by
  exact
    v17_globalPairEnergyNat_matrixNormSq450_eq_offDiagonalEnergy
      (v17Gram450 T s hs)
      (v17Gram450_norm_sq_comm T s hs)

/-- Analytic compact-overlap control plus the exact finite pair reindexing gives
the off-diagonal energy lower bound needed by the spectral step. -/
theorem v17_Gram450_kernel_pair_energy_lower_offDiagonal
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    globalPairEnergyNat 450 (limitingWeightOnPoints (v17Y450 T s hs)) -
        404100 * v17ArticleCompactError T M
      ≤
    offDiagonalEnergy (v17Gram450 T s hs) := by
  have h :=
    v17_Gram450_global_pair_energy_lower
      hPois hnorm hl hwL hsmall hM1 hM2 hkk s hs
  change
    globalPairEnergyNat 450 (limitingWeightOnPoints (v17Y450 T s hs)) -
        404100 * v17ArticleCompactError T M
      ≤
    globalPairEnergyNat 450
      (v17MatrixNormSqNat450 (v17Gram450 T s hs)) at h
  rw [v17_globalPairEnergyNat_Gram450_eq_offDiagonalEnergy T s hs] at h
  exact h

end HurtadoZeta23
