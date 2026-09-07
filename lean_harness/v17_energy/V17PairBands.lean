import HurtadoZeta23.DirectRedistribution
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- A truncated range is the triangular filter inside the ambient square. -/
lemma v17_range_sub_eq_triangle_filter (N r : ℕ) :
    Finset.range (N - r) =
      (Finset.range N).filter (fun a => r + a < N) := by
  ext a
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- Write a dependent triangular row as a fixed ambient range with an
indicator. -/
lemma v17_sum_range_sub_eq_triangle_ite
    (N r : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.range (N - r), f a) =
      ∑ a ∈ Finset.range N, if r + a < N then f a else 0 := by
  rw [v17_range_sub_eq_triangle_filter]
  rw [Finset.sum_filter]

/-- Finite Fubini on the triangular domain `r+a<N`.  This is the exact
combinatorial reindexing from separation-first pair sums to row-first pair
sums. -/
theorem v17_triangle_sum_comm
    (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ r ∈ Finset.range N,
        ∑ a ∈ Finset.range (N - r), f r a) =
      ∑ a ∈ Finset.range N,
        ∑ r ∈ Finset.range (N - a), f r a := by
  calc
    (∑ r ∈ Finset.range N,
        ∑ a ∈ Finset.range (N - r), f r a)
        = ∑ r ∈ Finset.range N,
            ∑ a ∈ Finset.range N,
              if r + a < N then f r a else 0 := by
                apply Finset.sum_congr rfl
                intro r hr
                exact v17_sum_range_sub_eq_triangle_ite N r (f r)
    _ = ∑ a ∈ Finset.range N,
          ∑ r ∈ Finset.range N,
            if r + a < N then f r a else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.range N,
          ∑ r ∈ Finset.range N,
            if a + r < N then f r a else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro r hr
              rw [Nat.add_comm r a]
    _ = ∑ a ∈ Finset.range N,
          ∑ r ∈ Finset.range (N - a), f r a := by
              apply Finset.sum_congr rfl
              intro a ha
              symm
              exact v17_sum_range_sub_eq_triangle_ite N a (fun r => f r a)

/-- The strict-upper pair energy written row-first in natural coordinates. -/
def v17UpperRowPairEnergyNat450 (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range 449,
    ∑ r ∈ Finset.range (449 - a), w a (a + r + 1)

/-- At length 450, the global directed pair energy is exactly twice the
row-first strict-upper triangular energy. -/
theorem v17_globalPairEnergyNat_450_eq_two_upperRows
    (w : ℕ → ℕ → ℝ) :
    globalPairEnergyNat 450 w = 2 * v17UpperRowPairEnergyNat450 w := by
  unfold globalPairEnergyNat pairBandEnergy v17UpperRowPairEnergyNat450
  norm_num
  have hsum :
      (∑ r ∈ Finset.range 449,
          ∑ a ∈ Finset.range (450 - (r + 1)), w a (a + r + 1)) =
        ∑ a ∈ Finset.range 449,
          ∑ r ∈ Finset.range (449 - a), w a (a + r + 1) := by
    calc
      (∑ r ∈ Finset.range 449,
          ∑ a ∈ Finset.range (450 - (r + 1)), w a (a + r + 1))
          = ∑ r ∈ Finset.range 449,
              ∑ a ∈ Finset.range (449 - r), w a (a + r + 1) := by
                apply Finset.sum_congr rfl
                intro r hr
                rw [show 450 - (r + 1) = 449 - r by omega]
      _ = ∑ a ∈ Finset.range 449,
            ∑ r ∈ Finset.range (449 - a), w a (a + r + 1) := by
              exact v17_triangle_sum_comm 449 (fun r a => w a (a + r + 1))
  exact hsum

end HurtadoZeta23
