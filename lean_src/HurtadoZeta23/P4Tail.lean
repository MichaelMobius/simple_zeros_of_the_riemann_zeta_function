import HurtadoZeta23.UniformGridTail
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- The p=4 tail beginning at the natural index `M`. -/
def p4Tail (M : ℕ) : ℝ :=
  ∑' k : ℕ, p4Majorant (k + M)

/-- The shifted p=4 tail tends to zero. -/
theorem tendsto_p4Tail_zero :
    Tendsto p4Tail atTop (nhds 0) := by
  change
    Tendsto
      (fun M : ℕ => ∑' k : ℕ, p4Majorant (k + M))
      atTop (nhds 0)
  exact tendsto_sum_nat_add p4Majorant

/-- Epsilon formulation of p=4 tail vanishing. -/
theorem eventually_p4Tail_lt {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, p4Tail M < eps := by
  have hopen : Set.Iio eps ∈ nhds (0 : ℝ) :=
    Iio_mem_nhds heps
  exact tendsto_p4Tail_zero.eventually hopen

/-- A tail beginning at `M` of an arbitrary real summand. -/
def shiftedTail (summand : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑' k : ℕ, summand (k + M)

/-- A clean comparison interface for a single omitted half-grid. -/
def ShiftedP4Majorized
    (summand : ℕ → ℝ) (A : ℝ) (M : ℕ) : Prop :=
  0 ≤ A ∧ ∀ k : ℕ,
    |summand (k + M)| ≤ A * p4Majorant (k + M)

/-- Comparison of an omitted half-grid with the scalar p=4 tail.

This uses Mathlib's direct `tsum_of_norm_bounded` comparison theorem, avoiding
an intermediate absolute-summability proof and a second `tsum` comparison. -/
theorem abs_shiftedTail_le_p4Tail
    {summand : ℕ → ℝ} {A : ℝ} {M : ℕ}
    (hmaj : ShiftedP4Majorized summand A M) :
    |shiftedTail summand M| ≤ A * p4Tail M := by
  rcases hmaj with ⟨_, hpoint⟩

  have hp4shift :
      Summable (fun k : ℕ => p4Majorant (k + M)) :=
    (summable_nat_add_iff M).2 summable_p4Majorant

  have hscaled :
      HasSum
        (fun k : ℕ => A * p4Majorant (k + M))
        (A * p4Tail M) := by
    unfold p4Tail
    exact hp4shift.hasSum.mul_left A

  have hbound :
      ‖∑' k : ℕ, summand (k + M)‖ ≤ A * p4Tail M := by
    exact tsum_of_norm_bounded hscaled (fun k => by
      simpa only [Real.norm_eq_abs] using hpoint k)

  simpa only [shiftedTail, Real.norm_eq_abs] using hbound

/-- Uniform epsilon-tail consequence of p=4 majorization. -/
theorem eventually_abs_shiftedTail_lt
    {A eps : ℝ} (hA : 0 ≤ A) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop,
      ∀ summand : ℕ → ℝ,
        ShiftedP4Majorized summand A M →
        |shiftedTail summand M| < eps := by
  by_cases hAz : A = 0
  · subst A
    filter_upwards with M
    intro summand hmaj
    have hle :
        |shiftedTail summand M| ≤
          (0 : ℝ) * p4Tail M :=
      abs_shiftedTail_le_p4Tail hmaj
    have hle0 :
        |shiftedTail summand M| ≤ 0 := by
      simpa only [zero_mul] using hle
    exact lt_of_le_of_lt hle0 heps
  · have hApos : 0 < A :=
      lt_of_le_of_ne hA (Ne.symm hAz)
    have htail :=
      eventually_p4Tail_lt
        (eps := eps / A) (div_pos heps hApos)
    filter_upwards [htail] with M hM
    intro summand hmaj
    have hle :=
      abs_shiftedTail_le_p4Tail hmaj
    have hmul :
        A * p4Tail M < eps := by
      calc
        A * p4Tail M < A * (eps / A) :=
          mul_lt_mul_of_pos_left hM hApos
        _ = eps := by
          field_simp [hAz]
    exact lt_of_le_of_lt hle hmul

end HurtadoZeta23
