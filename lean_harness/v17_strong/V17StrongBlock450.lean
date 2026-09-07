import HurtadoZeta23.V17WeightedPressure
import HurtadoZeta23.V17KernelBridge450
import HurtadoZeta23.V17StrongBlockScalar
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace HurtadoZeta23

/-!
# Abstract v17 strong block at length 450

This file contains only the finite/algebraic strong-block mechanism.  It is
intentionally independent of the concrete zeta kernel, retained columns, Gram
construction, PSD arguments, and the analytic compact-overlap estimate.

The concrete layer must provide five interfaces:

* a seven-point certificate for a nonnegative pair weight `w`;
* the one-gap weighted-pressure scalar inequality;
* a pointwise lower comparison `w - 2 eps <= gramSq`;
* adjacent Gram-band control `pairBandEnergy ... gramSq <= D`;
* exact global Gram-energy identification together with the spectral threshold.

Once those are supplied, the exact losses `898 eps` and `404100 eps` and the
rational scalar contradiction are entirely internal.
-/

theorem v17_strong_block_450_of_interfaces
    (y : ℕ → ℝ)
    (w gramSq : ℕ → ℕ → ℝ)
    (D O eps : ℝ)
    (heps : 0 ≤ eps)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert : SevenPointCertificate w y 450)
    (hscalar : ∀ q < 449,
      v17t * beta * v17g0 ≤
        w q (q + 1) +
          v17t * beta * (y (q + 1) - y q))
    (hpoint : ∀ a b, a < 450 → b < 450 →
      w a b - 2 * eps ≤ gramSq a b)
    (hband : pairBandEnergy 450 0 gramSq ≤ D)
    (hglobal : globalPairEnergyNat 450 gramSq = O)
    (hthreshold : D < O → v17FiniteThreshold < D) :
    v17A - 404100 * eps ≤
      D + v17LiteralBlockPressure 450 y := by
  let E : ℝ := globalPairEnergyNat 450 w
  let P : ℝ := v17LiteralBlockPressure 450 y

  have hEP : v17A ≤ E + P := by
    dsimp [E, P]
    exact v17_certificate_energy_pressure_450 y w hw hcert

  have hweightedKernel :
      v17t * v17g0 * v17Q ≤
        pairBandEnergy 450 0 w + v17t * P := by
    dsimp [P]
    exact v17_weighted_adjacent_pressure_450 y w hw hscalar

  have hadjBridge :
      pairBandEnergy 450 0 w - 898 * eps
        ≤ pairBandEnergy 450 0 gramSq := by
    apply v17_adjacent_kernel_lower_450_of_pointwise_raw_loss
    intro a ha
    exact hpoint a (a + 1) (by omega) (by omega)

  have hweighted :
      v17t * v17g0 * v17Q ≤ D + v17t * P + 898 * eps := by
    linarith

  have hglobalBridge : E - 404100 * eps ≤ O := by
    have hraw :
        globalPairEnergyNat 450 w - 404100 * eps
          ≤ globalPairEnergyNat 450 gramSq := by
      apply v17_aggregate_kernel_lower_450_of_pointwise_raw_loss
      exact hpoint
    dsimp [E]
    rw [hglobal] at hraw
    exact hraw

  have herr : 898 * eps ≤ v17t * (404100 * eps) :=
    v17_raw_error_absorption eps heps

  exact v17_strong_block_scalar_finite
    (D := D) (E := E) (O := O) (P := P)
    (eK := 404100 * eps) (eW := 898 * eps)
    hEP hweighted hglobalBridge hthreshold herr

end HurtadoZeta23