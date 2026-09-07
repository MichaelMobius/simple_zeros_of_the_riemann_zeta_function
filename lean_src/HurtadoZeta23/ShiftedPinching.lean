import HurtadoZeta23.ShiftedAveraging
import HurtadoZeta23.DirectRedistribution
import Mathlib.Tactic

namespace HurtadoZeta23

open scoped BigOperators

/-- Span of the consecutive block starting at `s`, written as a sum of gaps. -/
def slidingBlockSpan (g : ℕ → ℝ) (m s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m - 1), g (s + i)

/-- Total span of an ordered configuration, written in gap coordinates. -/
def totalGapSpan (g : ℕ → ℝ) (S : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (S - 1), g q

/--
Across *all* consecutive full blocks of length `m`, each global gap is used at
most `m-1` times.  This is the finite combinatorial core behind the averaging
over the `m` shifted block decompositions in the paper.
-/
theorem sum_slidingBlockSpan_le
    {S m : ℕ} (hm : 1 ≤ m) (hSm : m ≤ S)
    (g : ℕ → ℝ)
    (hg : ∀ q < S - 1, 0 ≤ g q) :
    (∑ s ∈ Finset.range (S - m + 1), slidingBlockSpan g m s)
      ≤ ((m - 1 : ℕ) : ℝ) * totalGapSpan g S := by
  unfold slidingBlockSpan totalGapSpan
  rw [Finset.sum_comm]
  have h_each : ∀ i ∈ Finset.range (m - 1),
      (∑ s ∈ Finset.range (S - m + 1), g (s + i))
        ≤ ∑ q ∈ Finset.range (S - 1), g q := by
    intro i hi
    apply sum_shifted_range_le_range
      (f := g)
      (hf := hg)
    have hi' : i < m - 1 := Finset.mem_range.mp hi
    omega
  calc
    (∑ i ∈ Finset.range (m - 1),
        ∑ s ∈ Finset.range (S - m + 1), g (s + i))
      ≤ ∑ i ∈ Finset.range (m - 1),
          (∑ q ∈ Finset.range (S - 1), g q) := by
            exact Finset.sum_le_sum h_each
    _ = ((m - 1 : ℕ) : ℝ) *
          (∑ q ∈ Finset.range (S - 1), g q) := by
            simp [Finset.card_range, mul_comm]

/-- Number of consecutive full blocks of length `m` among `S` ordered points. -/
def slidingBlockCount (S m : ℕ) : ℕ := S - m + 1

/-- For `m ≤ S`, the full-block count differs from `S` by exactly `m-1`. -/
lemma slidingBlockCount_cast
    {S m : ℕ} (hm : 1 ≤ m) (hSm : m ≤ S) :
    ((slidingBlockCount S m : ℕ) : ℝ) =
      (S : ℝ) - ((m - 1 : ℕ) : ℝ) := by
  unfold slidingBlockCount
  have hnat : S - m + 1 = S - (m - 1) := by
    omega
  rw [hnat]
  rw [Nat.cast_sub]
  omega

/--
Exact scalar form of shifted pinching before asymptotics.

`blockSum` is the sum of defects of *all* consecutive length-`m` blocks. The
`m` shifted pinchings imply `blockSum ≤ m * D`. Summed block stability gives
the lower bound on `blockSum`, while `spanSum` is controlled by the preceding
combinatorial lemma.
-/
theorem shifted_pinching_exact
    {S : ℕ}
    {D spanSum totalSpan err blockSum : ℝ}
    (hS : blockLength ≤ S)
    (hspan0 : 0 ≤ totalSpan)
    (hspan : spanSum ≤ ((blockLength - 1 : ℕ) : ℝ) * totalSpan)
    (hblocks :
      A0 * ((slidingBlockCount S blockLength : ℕ) : ℝ)
        - beta * spanSum - err ≤ blockSum)
    (hpinch : blockSum ≤ (blockLength : ℝ) * D) :
    alpha * (S : ℝ)
      - pressureCost * totalSpan
      - endpointCorrection
      - err / blockLength ≤ D := by

  have hm : (1 : ℕ) ≤ blockLength := by
    norm_num [blockLength]

  have hcount :
      ((slidingBlockCount S blockLength : ℕ) : ℝ) =
        (S : ℝ) - ((blockLength - 1 : ℕ) : ℝ) :=
    slidingBlockCount_cast hm hS

  have hbeta : 0 ≤ beta := by
    norm_num [beta]

  have hspan' :
      beta * spanSum ≤
        beta * (((blockLength - 1 : ℕ) : ℝ) * totalSpan) := by
    exact mul_le_mul_of_nonneg_left hspan hbeta

  have hraw :
      A0 * ((S : ℝ) - ((blockLength - 1 : ℕ) : ℝ))
        - beta * (((blockLength - 1 : ℕ) : ℝ) * totalSpan)
        - err
        ≤ (blockLength : ℝ) * D := by
    rw [← hcount]
    linarith

  norm_num [
    blockLength,
    alpha,
    pressureCost,
    beta,
    A0,
    delta,
    endpointCorrection
  ] at hraw ⊢

  linarith

/-- Exact coefficient specialization of the shifted-pinching inequality. -/
theorem shifted_pinching_published_coefficients
    {S : ℕ}
    {D spanSum totalSpan err blockSum : ℝ}
    (hS : blockLength ≤ S)
    (hspan0 : 0 ≤ totalSpan)
    (hspan : spanSum ≤ ((blockLength - 1 : ℕ) : ℝ) * totalSpan)
    (hblocks :
      A0 * ((slidingBlockCount S blockLength : ℕ) : ℝ)
        - beta * spanSum - err ≤ blockSum)
    (hpinch : blockSum ≤ (blockLength : ℝ) * D) :
    (312 / 81875 : ℝ) * (S : ℝ)
      - (261 / 131000 : ℝ) * totalSpan
      - endpointCorrection
      - err / blockLength ≤ D := by
  simpa [alpha, pressureCost] using
    shifted_pinching_exact hS hspan0 hspan hblocks hpinch

end HurtadoZeta23
