import HurtadoZeta23.ResearchNinePointHybrid
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-!
# Exact shifted assembly at block length 289

This is the dimension-289 analogue of the established v17 shifted assembly.
It is purely finite algebra: no analytic kernel, certificate verifier, or zeta
asymptotics enter here.
-/

/-- Coefficient of the retained-simple count in the global defect lower bound. -/
def research9Alpha : ℝ := research9A / 289

/-- Coefficient of total span/zero count in the global pressure loss. -/
def research9PressureCost : ℝ := research9Q / 289

/-- Finite endpoint loss from the 288 coordinates not covered by all shifted
length-289 blocks. -/
def research9EndpointCorrection : ℝ := research9A * 288 / 289

lemma research9_full_block_count_cast
    {S : ℕ} (hS : 289 ≤ S) :
    (((S - 289 + 1 : ℕ) : ℝ)) = (S : ℝ) - 288 := by
  have hnat : S - 289 + 1 = S - 288 := by omega
  have h288 : 288 ≤ S := by omega
  rw [hnat, Nat.cast_sub h288]
  norm_num

lemma research9_alpha_eq_A_div_289 :
    research9Alpha = research9A / 289 := rfl

lemma research9_pressureCost_eq_Q_div_289 :
    research9PressureCost = research9Q / 289 := rfl

/-- Exact shifted assembly from the sums of all complete length-289 blocks. -/
theorem research9_shifted_assembly_exact
    {S : ℕ}
    {D pressureSum totalSpan err blockSum : ℝ}
    (hS : 289 ≤ S)
    (hpressure : pressureSum ≤ research9Q * totalSpan)
    (hblocks :
      research9A * (((S - 289 + 1 : ℕ) : ℝ)) - err
        ≤ blockSum + pressureSum)
    (hpinch : blockSum ≤ (289 : ℝ) * D) :
    research9Alpha * (S : ℝ)
      - research9PressureCost * totalSpan
      - research9EndpointCorrection
      - err / 289 ≤ D := by
  have hcount := research9_full_block_count_cast hS
  have hraw :
      research9A * ((S : ℝ) - 288) - err
        ≤ (289 : ℝ) * D + research9Q * totalSpan := by
    rw [← hcount]
    linarith
  unfold research9Alpha research9PressureCost research9EndpointCorrection
  nlinarith

/-- Sum a uniform local strong-block inequality over all full length-289
blocks. -/
theorem research9_sum_uniform_local_blocks
    {S : ℕ} (hS : 289 ≤ S)
    {e : ℝ}
    (blockDef pressure : ℕ → ℝ)
    (hlocal : ∀ b < S - 289 + 1,
      research9A - e ≤ blockDef b + pressure b) :
    research9A * (((S - 289 + 1 : ℕ) : ℝ))
        - (((S - 289 + 1 : ℕ) : ℝ)) * e
      ≤
    (∑ b ∈ Finset.range (S - 289 + 1), blockDef b)
      + (∑ b ∈ Finset.range (S - 289 + 1), pressure b) := by
  have hsum :
      (∑ b ∈ Finset.range (S - 289 + 1), (research9A - e))
        ≤
      ∑ b ∈ Finset.range (S - 289 + 1),
        (blockDef b + pressure b) := by
    apply Finset.sum_le_sum
    intro b hb
    exact hlocal b (Finset.mem_range.mp hb)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

/-- Exact finite shifted assembly directly from uniform local block bounds,
pressure averaging, and the 289-fold principal-block pinching estimate. -/
theorem research9_shifted_assembly_from_uniform_blocks
    {S : ℕ} (hS : 289 ≤ S)
    {D totalSpan e : ℝ}
    (blockDef pressure : ℕ → ℝ)
    (hlocal : ∀ b < S - 289 + 1,
      research9A - e ≤ blockDef b + pressure b)
    (hpressure :
      (∑ b ∈ Finset.range (S - 289 + 1), pressure b)
        ≤ research9Q * totalSpan)
    (hpinch :
      (∑ b ∈ Finset.range (S - 289 + 1), blockDef b)
        ≤ (289 : ℝ) * D) :
    research9Alpha * (S : ℝ)
      - research9PressureCost * totalSpan
      - research9EndpointCorrection
      - ((((S - 289 + 1 : ℕ) : ℝ)) * e) / 289
      ≤ D := by
  apply research9_shifted_assembly_exact hS hpressure
  · exact research9_sum_uniform_local_blocks hS blockDef pressure hlocal
  · exact hpinch

/-- Exact identity for the projected research constant in terms of the global
assembly coefficients. -/
theorem research9_projectedBound_eq_global_coefficients :
    research9ProjectedBound =
      (research9Hcert - research9PressureCost) / (1 - research9Alpha) := by
  norm_num [research9ProjectedBound, research9Hcert,
    research9PressureCost, research9Alpha, research9Q, research9A]

end HurtadoZeta23
