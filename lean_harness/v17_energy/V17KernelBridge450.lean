import HurtadoZeta23.DirectRedistribution
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
  unfold globalPairEnergyNat
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro r0 hr0
    unfold pairBandEnergy
    apply Finset.sum_le_sum
    intro a ha
    exact hpoint a (a + r0 + 1)
  · norm_num

/-- Clean 450-point interface for the analytic overlap bridge.

The analytic input required downstream is exactly a pointwise lower bound on
squared Gram entries with loss `2*eps`.  No 262-point hypothesis is reused
here.  Once this pointwise statement is supplied for the actual finite Gram
block, the total directed pair-energy loss is exactly `404100*eps`. -/
theorem v17_aggregate_kernel_lower_450_of_pointwise_raw_loss
    (w gramSq : ℕ → ℕ → ℝ)
    (eps : ℝ)
    (hpoint : ∀ a b, w a b - 2 * eps ≤ gramSq a b) :
    globalPairEnergyNat 450 w - 404100 * eps
      ≤ globalPairEnergyNat 450 gramSq := by
  have hs := v17_aggregate_kernel_lower_450 w gramSq (2 * eps) hpoint
  have hcoeff : (202050 : ℝ) * (2 * eps) = 404100 * eps := by ring
  rw [hcoeff] at hs
  exact hs

/-- Subtracting a uniform error `eta` from each of the 449 adjacent entries
costs exactly `449*eta` in the first pair band. -/
lemma v17_pairBandEnergy_zero_sub_uniform_450
    (w : ℕ → ℕ → ℝ)
    (eta : ℝ) :
    pairBandEnergy 450 0 (fun a b => w a b - eta)
      = pairBandEnergy 450 0 w - 449 * eta := by
  unfold pairBandEnergy
  norm_num
  simp_rw [Finset.sum_sub_distrib]
  simp

/-- The adjacent 449-entry analogue of the global energy bridge.  A pointwise
loss of `2*eps` on adjacent squared entries aggregates to exactly
`898*eps`. -/
theorem v17_adjacent_kernel_lower_450_of_pointwise_raw_loss
    (w gramSq : ℕ → ℕ → ℝ)
    (eps : ℝ)
    (hpoint : ∀ a < 449, w a (a + 1) - 2 * eps ≤ gramSq a (a + 1)) :
    pairBandEnergy 450 0 w - 898 * eps
      ≤ pairBandEnergy 450 0 gramSq := by
  have hmono :
      pairBandEnergy 450 0 (fun a b => w a b - 2 * eps)
        ≤ pairBandEnergy 450 0 gramSq := by
    change (∑ a ∈ Finset.range 449, (w a (a + 1) - 2 * eps))
      ≤ ∑ a ∈ Finset.range 449, gramSq a (a + 1)
    apply Finset.sum_le_sum
    intro a ha
    exact hpoint a (Finset.mem_range.mp ha)
  rw [v17_pairBandEnergy_zero_sub_uniform_450 w (2 * eps)] at hmono
  have hcoeff : (449 : ℝ) * (2 * eps) = 898 * eps := by ring
  rw [hcoeff] at hmono
  exact hmono

end HurtadoZeta23
