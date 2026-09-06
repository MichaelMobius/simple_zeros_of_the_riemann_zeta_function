import HurtadoZeta23.DirectRedistribution
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- Split the first `2*n+1` natural indices into the `n+1` even positions and
`n` odd positions.  This is the combinatorial identity needed to recombine the
two adjacent matchings at length 450. -/
theorem v17_sum_range_two_mul_add_one_split
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ Finset.range (2 * n + 1), f q) =
      (∑ b ∈ Finset.range (n + 1), f (2 * b)) +
      (∑ b ∈ Finset.range n, f (2 * b + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

/-- The 449 adjacent positions split into 225 even starts and 224 odd starts. -/
theorem v17_sum_range_449_even_odd
    (f : ℕ → ℝ) :
    (∑ q ∈ Finset.range 449, f q) =
      (∑ b ∈ Finset.range 225, f (2 * b)) +
      (∑ b ∈ Finset.range 224, f (2 * b + 1)) := by
  simpa using v17_sum_range_two_mul_add_one_split f 224

/-- The first adjacent pair band at length 450 is exactly its even-start and
odd-start parts. -/
theorem v17_pairBandEnergy_450_even_odd
    (w : ℕ → ℕ → ℝ) :
    pairBandEnergy 450 0 w =
      (∑ b ∈ Finset.range 225, w (2 * b) (2 * b + 1)) +
      (∑ b ∈ Finset.range 224, w (2 * b + 1) (2 * b + 2)) := by
  unfold pairBandEnergy
  norm_num
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    v17_sum_range_449_even_odd (fun q => w q (q + 1))

end HurtadoZeta23
