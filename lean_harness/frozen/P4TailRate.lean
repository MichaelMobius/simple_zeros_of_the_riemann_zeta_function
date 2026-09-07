import HurtadoZeta23.P4Tail
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Explicit rate for the p=4 tail

For the final Input-IV asymptotics we do not need the sharp
`p4Tail M = O(M^{-3})`.

The weaker bound

  `p4Tail M <= C / M^2`

already suffices because the article chooses an endpoint margin
`M(T) ≍ l(T)^2`, while the normalized Fourier-tail prefactor grows only like
`l(T)^2`.

The proof compares

  1 / (k+M)^4

with

  (1/M^2) * 1/(k+1)^2

and sums the fixed p=2 majorant.
-/

/-- Fixed shifted p=2 majorant. -/
def p2ShiftMajorant (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℕ) : ℝ) ^ 2)

/-- The shifted p=2 majorant is summable. -/
theorem summable_p2ShiftMajorant :
    Summable p2ShiftMajorant := by

  have h2 :
      Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
    simpa using
      (Real.summable_one_div_nat_pow (p := 2)).2
        (by norm_num)

  have hs :
      Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    exact (summable_nat_add_iff 1).2 h2

  exact hs

/-- The finite constant used in the weak `M^{-2}` tail estimate. -/
def p2ShiftSum : ℝ :=
  ∑' k : ℕ, p2ShiftMajorant k

theorem p2ShiftSum_nonneg :
    0 ≤ p2ShiftSum := by
  unfold p2ShiftSum
  apply tsum_nonneg
  intro k
  unfold p2ShiftMajorant
  positivity

/--
Pointwise comparison

`(k+M)^(-4) <= M^(-2) (k+1)^(-2)`

for `M >= 1`.
-/
theorem p4Majorant_add_le_inv_sq_mul_p2
    {M : ℕ}
    (hM : 1 ≤ M)
    (k : ℕ) :
    p4Majorant (k + M)
      ≤
    (1 / ((M : ℝ) ^ 2)) * p2ShiftMajorant k := by

  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)

  have hk1pos :
      (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    positivity

  have hnposNat :
      0 < k + M := by
    omega

  have hnpos :
      (0 : ℝ) < ((k + M : ℕ) : ℝ) := by
    exact_mod_cast hnposNat

  have hMle :
      (M : ℝ) ≤ ((k + M : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left M k

  have hk1le :
      (((k + 1 : ℕ) : ℝ))
        ≤ ((k + M : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hM k

  have hM2 :
      (M : ℝ) ^ 2
        ≤ ((k + M : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (((k + M : ℕ) : ℝ) - (M : ℝ))]

  have hk2 :
      (((k + 1 : ℕ) : ℝ)) ^ 2
        ≤ ((k + M : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (((k + M : ℕ) : ℝ) - (((k + 1 : ℕ) : ℝ)))]

  have hden :
      (M : ℝ) ^ 2 * (((k + 1 : ℕ) : ℝ)) ^ 2
        ≤
      ((k + M : ℕ) : ℝ) ^ 4 := by
    calc
      (M : ℝ) ^ 2 * (((k + 1 : ℕ) : ℝ)) ^ 2
          ≤
        ((k + M : ℕ) : ℝ) ^ 2 *
          ((k + M : ℕ) : ℝ) ^ 2 := by
            exact
              mul_le_mul
                hM2
                hk2
                (sq_nonneg _)
                (sq_nonneg _)

      _ = ((k + M : ℕ) : ℝ) ^ 4 := by
            ring

  have hsmall :
      1 / (((k + M : ℕ) : ℝ) ^ 4)
        ≤
      1 /
        ((M : ℝ) ^ 2 *
          (((k + 1 : ℕ) : ℝ)) ^ 2) := by

    exact
      one_div_le_one_div_of_le
        (mul_pos (pow_pos hMpos 2) (pow_pos hk1pos 2))
        hden

  unfold p4Majorant p2ShiftMajorant

  calc
    1 / (((k + M : ℕ) : ℝ) ^ 4)
        ≤
      1 /
        ((M : ℝ) ^ 2 *
          (((k + 1 : ℕ) : ℝ)) ^ 2) :=
      hsmall

    _ =
      (1 / ((M : ℝ) ^ 2)) *
        (1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
          field_simp

/--
Weak quantitative tail estimate sufficient for the article:

`p4Tail M <= p2ShiftSum / M^2`.
-/
theorem p4Tail_le_p2ShiftSum_div_sq
    {M : ℕ}
    (hM : 1 ≤ M) :
    p4Tail M
      ≤
    p2ShiftSum / ((M : ℝ) ^ 2) := by

  have hp4sum :
      Summable (fun k : ℕ => p4Majorant (k + M)) :=
    (summable_nat_add_iff M).2 summable_p4Majorant

  have hp2sum :
      Summable p2ShiftMajorant :=
    summable_p2ShiftMajorant

  have hscaled :
      HasSum
        (fun k : ℕ =>
          (1 / ((M : ℝ) ^ 2)) * p2ShiftMajorant k)
        ((1 / ((M : ℝ) ^ 2)) * p2ShiftSum) := by

    unfold p2ShiftSum
    exact hp2sum.hasSum.mul_left
      (1 / ((M : ℝ) ^ 2))

  have hle :
      (∑' k : ℕ, p4Majorant (k + M))
        ≤
      ∑' k : ℕ,
        (1 / ((M : ℝ) ^ 2)) *
          p2ShiftMajorant k := by

    exact
      Summable.tsum_le_tsum
        (fun k =>
          p4Majorant_add_le_inv_sq_mul_p2 hM k)
        hp4sum
        hscaled.summable

  unfold p4Tail

  calc
    (∑' k : ℕ, p4Majorant (k + M))
        ≤
      ∑' k : ℕ,
        (1 / ((M : ℝ) ^ 2)) *
          p2ShiftMajorant k :=
      hle

    _ =
      (1 / ((M : ℝ) ^ 2)) * p2ShiftSum :=
      hscaled.tsum_eq

    _ =
      p2ShiftSum / ((M : ℝ) ^ 2) := by
        ring

end HurtadoZeta23
