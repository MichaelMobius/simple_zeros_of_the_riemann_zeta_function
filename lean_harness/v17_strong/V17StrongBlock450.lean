import HurtadoZeta23.V17WeightedPressure
import HurtadoZeta23.V17ScalarPressure
import HurtadoZeta23.V17KernelBridge450
import HurtadoZeta23.V17GramEnergy450
import HurtadoZeta23.V17AdjacentBand450
import HurtadoZeta23.V17GramThreshold450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Fully assembled v17 strong block at length 450

This theorem joins the already isolated interfaces:

* seven-point certificate -> `A ≤ E + P`;
* scalar-pressure frontier -> weighted adjacent lower bound;
* pointwise kernel/Gram comparison -> `404100 eps` global loss and `898 eps`
  adjacent loss;
* two finite matchings -> adjacent Gram band ≤ spectral defect;
* one-sided trace spectral threshold -> `5011/5000 < D` whenever `D < O`;
* the exact rational scalar finisher.

No asymptotic or shifted-block averaging occurs here.
-/

theorem v17_strong_block_450_of_interfaces
    (y : ℕ → ℝ)
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i, (G i i).re ≤ 1)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hcert : SevenPointCertificate (limitingWeightOnPoints y) y 450)
    (hy : ∀ q < 449, y q ≤ y (q + 1))
    (hnum : V17KernelAtCertPointClaim)
    (hmono : V17KernelAntitoneOnUnitClaim)
    (hpoint : ∀ a b, a < 450 → b < 450 →
      limitingWeightOnPoints y a b - 2 * eps
        ≤ v17MatrixNormSqNat450 G a b) :
    v17A - 404100 * eps ≤
      gramSpectralDefect G hG + v17LiteralBlockPressure 450 y := by
  let E : ℝ := globalPairEnergyNat 450 (limitingWeightOnPoints y)
  let P : ℝ := v17LiteralBlockPressure 450 y
  let D : ℝ := gramSpectralDefect G hG
  let O : ℝ := offDiagonalEnergy G

  have hw : ∀ a b, 0 ≤ limitingWeightOnPoints y a b := by
    intro a b
    unfold limitingWeightOnPoints
    exact limitingWeight_nonneg _

  have hEP : v17A ≤ E + P := by
    dsimp [E, P]
    exact v17_certificate_energy_pressure_450 y (limitingWeightOnPoints y) hw hcert

  have hscalar : ∀ q < 449,
      v17t * beta * v17g0 ≤
        limitingWeightOnPoints y q (q + 1) +
          v17t * beta * (y (q + 1) - y q) :=
    v17_scalar_pressure_on_points_of_frontiers hnum hmono y hy

  have hweightedKernel :
      v17t * v17g0 * v17Q ≤
        pairBandEnergy 450 0 (limitingWeightOnPoints y) + v17t * P := by
    dsimp [P]
    exact v17_weighted_adjacent_pressure_450
      y (limitingWeightOnPoints y) hw hscalar

  have hadjBridge :
      pairBandEnergy 450 0 (limitingWeightOnPoints y) - 898 * eps
        ≤ pairBandEnergy 450 0 (v17MatrixNormSqNat450 G) := by
    apply v17_adjacent_kernel_lower_450_of_pointwise_raw_loss
    intro a ha
    exact hpoint a (a + 1) ha (by omega)

  have hbandGram :
      pairBandEnergy 450 0 (v17MatrixNormSqNat450 G) ≤ D := by
    dsimp [D]
    have h := v17_adjacent_matrix_band_le_defect_450 G hG hdiag
    simpa [v17MatrixNormSqNat450, v17MatchingNormSqNat450] using h

  have hweighted :
      v17t * v17g0 * v17Q ≤ D + v17t * P + 898 * eps := by
    linarith

  have hglobalBridge : E - 404100 * eps ≤ O := by
    have hraw :
        globalPairEnergyNat 450 (limitingWeightOnPoints y) - 404100 * eps
          ≤ globalPairEnergyNat 450 (v17MatrixNormSqNat450 G) := by
      apply v17_aggregate_kernel_lower_450_of_pointwise_raw_loss
      exact hpoint
    have hcomm : ∀ i j : Fin 450,
        ‖G i j‖ ^ 2 = ‖G j i‖ ^ 2 := by
      intro i j
      calc
        ‖G i j‖ ^ 2 = ‖star (G j i)‖ ^ 2 := by
          rw [(hG.isHermitian.apply i j).symm]
        _ = ‖G j i‖ ^ 2 := by simp
    have hid :=
      v17_globalPairEnergyNat_matrixNormSq450_eq_offDiagonalEnergy G hcomm
    dsimp [E, O]
    rw [hid] at hraw
    exact hraw

  have hthreshold : D < O → v17FiniteThreshold < D := by
    intro hDO
    dsimp [D, O] at hDO ⊢
    exact v17_psd_gram_threshold_450_of_diag G hG hdiag hDO

  have herr : 898 * eps ≤ v17t * (404100 * eps) :=
    v17_raw_error_absorption eps heps

  exact v17_strong_block_scalar_finite
    (D := D) (E := E) (O := O) (P := P)
    (eK := 404100 * eps) (eW := 898 * eps)
    hEP hweighted hglobalBridge hthreshold herr

end HurtadoZeta23
