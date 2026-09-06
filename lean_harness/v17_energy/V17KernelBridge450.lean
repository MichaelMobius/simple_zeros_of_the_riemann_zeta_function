import HurtadoZeta23.PoissonGaborBridge
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- There are `binom 450 2 = 101025` unordered pairs in a 450-point block. -/
lemma v17_pairMultiplicitySumNat_450 :
    (∑ x ∈ Finset.range 449, (450 - (1 + x))) = 101025 := by
  native_decide

lemma v17_pairMultiplicitySum_450 :
    (∑ x ∈ Finset.range 449,
      ((450 - (1 + x) : ℕ) : ℝ)) = 101025 := by
  exact_mod_cast v17_pairMultiplicitySumNat_450

/-- Subtracting a uniform per-unordered-pair error `eta` from a 450-point
kernel costs exactly `202050 * eta` in the directed pair energy. -/
lemma v17_globalPairEnergyNat_sub_uniform_450
    (w : ℕ → ℕ → ℝ)
    (eta : ℝ) :
    globalPairEnergyNat 450 (fun a b => w a b - eta)
      = globalPairEnergyNat 450 w - 202050 * eta := by
  unfold globalPairEnergyNat pairBandEnergy
  norm_num
  have hsum :
      (∑ x ∈ Finset.range 449,
        ((450 - (x + 1) : ℕ) : ℝ)) = 101025 := by
    simpa [Nat.add_comm] using v17_pairMultiplicitySum_450
  have hcount :
      (∑ x ∈ Finset.range 449,
        ((450 - (x + 1) : ℕ) : ℝ) * eta) = 101025 * eta := by
    calc
      (∑ x ∈ Finset.range 449,
        ((450 - (x + 1) : ℕ) : ℝ) * eta)
          = (∑ x ∈ Finset.range 449,
              ((450 - (x + 1) : ℕ) : ℝ)) * eta := by
              rw [← Finset.sum_mul]
      _ = 101025 * eta := by rw [hsum]
  rw [hcount]
  ring

/-- Uniform squared-entry lower approximation aggregated over 450 points. -/
theorem v17_aggregate_kernel_lower_450
    (w gramSq : ℕ → ℕ → ℝ)
    (eta : ℝ)
    (hpoint : ∀ a b, w a b - eta ≤ gramSq a b) :
    globalPairEnergyNat 450 w - 202050 * eta
      ≤ globalPairEnergyNat 450 gramSq := by
  rw [← v17_globalPairEnergyNat_sub_uniform_450 w eta]
  exact globalPairEnergyNat_mono hpoint

/-- A raw overlap error `eps` costs at most `404100 * eps` in the 450-point
directed pair energy.  The factor two comes from squaring overlaps. -/
theorem v17_aggregate_kernel_lower_450_of_raw
    (y : ℕ → ℝ)
    (overlap : ℕ → ℕ → ℝ)
    (eps : ℝ)
    (h : RawPointwiseOverlapApproximation262 y overlap eps) :
    globalPairEnergyNat 450 (limitingWeightOnPoints y)
        - 404100 * eps
      ≤ globalPairEnergyNat 450 (fun a b => overlap a b ^ 2) := by
  have hp := pointwiseKernelApproximation262_of_raw y overlap eps h
  have hs := v17_aggregate_kernel_lower_450
    (limitingWeightOnPoints y)
    (fun a b => overlap a b ^ 2)
    (2 * eps)
    hp.2
  have hcoeff : (202050 : ℝ) * (2 * eps) = 404100 * eps := by
    ring
  rw [hcoeff] at hs
  exact hs

end HurtadoZeta23
