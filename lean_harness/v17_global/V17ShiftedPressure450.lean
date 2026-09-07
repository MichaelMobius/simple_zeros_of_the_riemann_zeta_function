import HurtadoZeta23.V17WeightedPressure
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- Literal v17 pressure of the length-450 block beginning at global index `b`. -/
def v17ShiftedLiteralPressure450 (y : ℕ → ℝ) (b : ℕ) : ℝ :=
  v17LiteralBlockPressure 450 (fun i => y (b + i))

/-- For a fixed local window position and pressure coordinate, summing that
shifted gap over all length-450 block starts costs at most one copy of the
complete global gap span. -/
lemma v17_shifted_window_gap_sum_le_span
    {S : ℕ} (hS : 450 ≤ S)
    (y : ℕ → ℝ)
    (hmono : ∀ q < S - 1, y q ≤ y (q + 1))
    (s : ℕ) (hs : s < 444) (j : Fin 6) :
    (∑ b ∈ Finset.range (S - 450 + 1),
        windowGap (fun i => y (b + i)) s j)
      ≤ y (S - 1) - y 0 := by
  have hshift :=
    sum_shifted_range_le_range
      (f := fun q => y (q + 1) - y q)
      (hf := fun q hq => sub_nonneg.mpr (hmono q hq))
      (n := S - 450 + 1)
      (k := s + j.1)
      (N := S - 1)
      (by
        have hj : j.1 < 6 := j.2
        omega)
  have htel := telescoping_gap_sum y (S - 1)
  rw [htel] at hshift
  simpa [windowGap, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hshift

/-- Exact v17 shifted-pressure averaging.

For every local window position `s=0,...,443` and every pressure coordinate
`j=0,...,5`, the shifted copy of the global gap sequence injects into the
complete global gap range.  Summing first in the block start, then in `j`, and
finally in the 444 seven-point windows therefore costs exactly

`444 * beta = 111/125 = v17Q`

copies of the global span.  This is the pressure-preserving coefficient used
by v17, replacing the older coarse `beta * 449` bound. -/
theorem v17_sum_shifted_literal_pressure450_le
    {S : ℕ} (hS : 450 ≤ S)
    (y : ℕ → ℝ)
    (hmono : ∀ q < S - 1, y q ≤ y (q + 1)) :
    (∑ b ∈ Finset.range (S - 450 + 1),
        v17ShiftedLiteralPressure450 y b)
      ≤ v17Q * (y (S - 1) - y 0) := by
  have hreorder :
      (∑ b ∈ Finset.range (S - 450 + 1),
          v17ShiftedLiteralPressure450 y b)
        =
      ∑ s ∈ Finset.range 444,
        ∑ j : Fin 6,
          pressure j *
            (∑ b ∈ Finset.range (S - 450 + 1),
              windowGap (fun i => y (b + i)) s j) := by
    unfold v17ShiftedLiteralPressure450 v17LiteralBlockPressure localPressure
    norm_num
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum]

  rw [hreorder]
  calc
    (∑ s ∈ Finset.range 444,
        ∑ j : Fin 6,
          pressure j *
            (∑ b ∈ Finset.range (S - 450 + 1),
              windowGap (fun i => y (b + i)) s j))
      ≤
    ∑ s ∈ Finset.range 444,
      ∑ j : Fin 6,
        pressure j * (y (S - 1) - y 0) := by
          apply Finset.sum_le_sum
          intro s hs
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left
            (v17_shifted_window_gap_sum_le_span
              hS y hmono s (Finset.mem_range.mp hs) j)
            (pressure_nonneg j)
    _ = (444 : ℝ) * beta * (y (S - 1) - y 0) := by
          rw [← Finset.sum_mul]
          rw [pressure_sum]
          simp
          ring
    _ = v17Q * (y (S - 1) - y 0) := by
          norm_num [beta, v17Q]

end HurtadoZeta23