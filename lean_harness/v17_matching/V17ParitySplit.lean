import HurtadoZeta23.DirectRedistribution
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/-- Split an even initial range into consecutive pairs.  Stating this
intermediate identity keeps the successor arithmetic away from the final
449-term specialization. -/
theorem v17_sum_range_two_mul_pairs
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ Finset.range (2 * n), f q) =
      ∑ b ∈ Finset.range n, (f (2 * b) + f (2 * b + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ q ∈ Finset.range (2 * (n + 1)), f q)
            = (∑ q ∈ Finset.range (2 * n), f q) +
                f (2 * n) + f (2 * n + 1) := by
                  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
                  rw [Finset.sum_range_succ]
                  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
                  rw [Finset.sum_range_succ]
        _ = (∑ b ∈ Finset.range n, (f (2 * b) + f (2 * b + 1))) +
              (f (2 * n) + f (2 * n + 1)) := by rw [ih]; ring
        _ = ∑ b ∈ Finset.range (n + 1),
              (f (2 * b) + f (2 * b + 1)) := by
                rw [Finset.sum_range_succ]

/-- Split the first `2*n+1` natural indices into the `n+1` even positions and
`n` odd positions. -/
theorem v17_sum_range_two_mul_add_one_split
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ Finset.range (2 * n + 1), f q) =
      (∑ b ∈ Finset.range (n + 1), f (2 * b)) +
      (∑ b ∈ Finset.range n, f (2 * b + 1)) := by
  calc
    (∑ q ∈ Finset.range (2 * n + 1), f q)
        = (∑ q ∈ Finset.range (2 * n), f q) + f (2 * n) := by
            rw [show 2 * n + 1 = (2 * n) + 1 by omega]
            rw [Finset.sum_range_succ]
    _ = (∑ b ∈ Finset.range n, (f (2 * b) + f (2 * b + 1))) +
          f (2 * n) := by rw [v17_sum_range_two_mul_pairs f n]
    _ = ((∑ b ∈ Finset.range n, f (2 * b)) + f (2 * n)) +
          (∑ b ∈ Finset.range n, f (2 * b + 1)) := by
            rw [Finset.sum_add_distrib]
            ring
    _ = (∑ b ∈ Finset.range (n + 1), f (2 * b)) +
          (∑ b ∈ Finset.range n, f (2 * b + 1)) := by
            rw [Finset.sum_range_succ]

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
  have h := v17_sum_range_449_even_odd (fun q => w q (q + 1))
  calc
    (∑ q ∈ Finset.range 449, w q (q + 1))
        = (∑ b ∈ Finset.range 225, w (2 * b) (2 * b + 1)) +
          (∑ b ∈ Finset.range 224, w (2 * b + 1) ((2 * b + 1) + 1)) := by
            simpa using h
    _ = (∑ b ∈ Finset.range 225, w (2 * b) (2 * b + 1)) +
          (∑ b ∈ Finset.range 224, w (2 * b + 1) (2 * b + 2)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro b hb
            congr 1
            omega

end HurtadoZeta23
