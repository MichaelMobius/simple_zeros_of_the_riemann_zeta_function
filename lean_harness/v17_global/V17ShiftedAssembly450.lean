import HurtadoZeta23.V17ShiftedPressure450
import HurtadoZeta23.V17Endgame
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- Finite endpoint loss caused by having `S-449` complete length-450 blocks. -/
def v17EndpointCorrection : ℝ := v17A * 449 / 450

lemma v17_full_block_count_cast
    {S : ℕ} (hS : 450 ≤ S) :
    (((S - 450 + 1 : ℕ) : ℝ)) = (S : ℝ) - 449 := by
  have hnat : S - 450 + 1 = S - 449 := by omega
  rw [hnat]
  rw [Nat.cast_sub]
  omega

lemma v17_alpha_eq_v17A_div_450 :
    v17Alpha = v17A / 450 := by
  norm_num [v17Alpha, v17A]

lemma v17_pressureCost_eq_v17Q_div_450 :
    v17PressureCost = v17Q / 450 := by
  norm_num [v17PressureCost, v17Q]

/-- Exact scalar shifted assembly for v17.

`blockSum` is the sum of spectral defects of all consecutive length-450
blocks, `pressureSum` is the sum of their literal pressure terms, and `err`
is the total accumulated finite-T error. -/
theorem v17_shifted_assembly_exact
    {S : ℕ}
    {D pressureSum totalSpan err blockSum : ℝ}
    (hS : 450 ≤ S)
    (hpressure : pressureSum ≤ v17Q * totalSpan)
    (hblocks :
      v17A * (((S - 450 + 1 : ℕ) : ℝ)) - err
        ≤ blockSum + pressureSum)
    (hpinch : blockSum ≤ (450 : ℝ) * D) :
    v17Alpha * (S : ℝ)
      - v17PressureCost * totalSpan
      - v17EndpointCorrection
      - err / 450 ≤ D := by
  have hcount := v17_full_block_count_cast hS
  have hraw :
      v17A * ((S : ℝ) - 449) - err
        ≤ (450 : ℝ) * D + v17Q * totalSpan := by
    rw [← hcount]
    linarith
  norm_num [v17Alpha, v17PressureCost, v17EndpointCorrection, v17A, v17Q] at hraw ⊢
  linarith

/-- Summing a uniform local strong-block inequality over all full length-450
blocks. -/
theorem v17_sum_uniform_local_blocks
    {S : ℕ} (hS : 450 ≤ S)
    {e : ℝ}
    (blockDef pressure : ℕ → ℝ)
    (hlocal : ∀ b < S - 450 + 1,
      v17A - e ≤ blockDef b + pressure b) :
    v17A * (((S - 450 + 1 : ℕ) : ℝ))
        - (((S - 450 + 1 : ℕ) : ℝ)) * e
      ≤
    (∑ b ∈ Finset.range (S - 450 + 1), blockDef b)
      + (∑ b ∈ Finset.range (S - 450 + 1), pressure b) := by
  have hsum :
      (∑ b ∈ Finset.range (S - 450 + 1), (v17A - e))
        ≤
      ∑ b ∈ Finset.range (S - 450 + 1),
        (blockDef b + pressure b) := by
    apply Finset.sum_le_sum
    intro b hb
    exact hlocal b (Finset.mem_range.mp hb)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

/-- Exact finite v17 assembly directly from uniform local block bounds,
pressure averaging, and the 450-fold principal-block pinching estimate. -/
theorem v17_shifted_assembly_from_uniform_blocks
    {S : ℕ} (hS : 450 ≤ S)
    {D totalSpan e : ℝ}
    (blockDef pressure : ℕ → ℝ)
    (hlocal : ∀ b < S - 450 + 1,
      v17A - e ≤ blockDef b + pressure b)
    (hpressure :
      (∑ b ∈ Finset.range (S - 450 + 1), pressure b)
        ≤ v17Q * totalSpan)
    (hpinch :
      (∑ b ∈ Finset.range (S - 450 + 1), blockDef b)
        ≤ (450 : ℝ) * D) :
    v17Alpha * (S : ℝ)
      - v17PressureCost * totalSpan
      - v17EndpointCorrection
      - ((((S - 450 + 1 : ℕ) : ℝ)) * e) / 450
      ≤ D := by
  apply v17_shifted_assembly_exact hS hpressure
  · exact v17_sum_uniform_local_blocks hS blockDef pressure hlocal
  · exact hpinch

end HurtadoZeta23
