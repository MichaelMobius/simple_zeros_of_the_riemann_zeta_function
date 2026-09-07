import HurtadoZeta23.ConcreteShiftedPinching
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Uniform block assembly

This file removes the global `hblocks` input from `ConcreteShiftedPinching`.

The manuscript's Uniform block stability lemma has the pointwise form

`A0 - beta * span(B) - localErr ≤ D(G_B)`

for every consecutive retained block `B`, with one error `localErr` that is
uniform over all such blocks.  Summing over all full consecutive blocks gives
the exact finite input required by shifted pinching.

After division by the `blockLength = 262` shifted decompositions, the final
error is

`(# full consecutive blocks / 262) * localErr`.

Thus the remaining mathematical task is genuinely local: prove the uniform
block inequality for one arbitrary consecutive retained block.
-/

/-- The number of full consecutive article blocks, as a real number. -/
def articleConsecutiveBlockCountR (T : ℝ) : ℝ :=
  ((slidingBlockCount (articleRetainedCard T) blockLength : ℕ) : ℝ)

/-- Error left after averaging a uniform per-block error over the 262 shifts. -/
def articleAveragedBlockError
    (T localErr : ℝ) : ℝ :=
  articleConsecutiveBlockCountR T * localErr / blockLength

/--
The gap-coordinate span sum is exactly the sum of the geometric spans of all
consecutive retained 262-blocks.
-/
theorem articleConsecutiveSpanSum_eq_finSum
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T) :
    articleConsecutiveSpanSum T
      =
    ∑ s : Fin (articleRetainedCard T - blockLength + 1),
      consecutiveBlockSpan
        T s.1
        (by
          have hs := s.2
          omega) := by

  unfold articleConsecutiveSpanSum

  rw [Finset.sum_range]

  apply Finset.sum_congr rfl
  intro s hs

  have hfit :
      s.1 + blockLength ≤ articleRetainedCard T := by
    have hslt := s.2
    omega

  exact
    slidingBlockSpan_articleRetainedGap_eq
      T s.1 hfit

/--
Summing a uniform local block-stability inequality over all consecutive
262-blocks gives the exact global `hblocks` inequality, with accumulated
error `(#blocks) * localErr`.
-/
theorem article_summed_uniform_block_stability
    (T localErr : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hlocal :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        A0
            - beta *
                consecutiveBlockSpan
                  T s.1
                  (by
                    have hs := s.2
                    omega)
            - localErr
          ≤
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            omega)) :
    A0 * articleConsecutiveBlockCountR T
        - beta * articleConsecutiveSpanSum T
        - articleConsecutiveBlockCountR T * localErr
      ≤
    articleConsecutiveBlockDefectSum T := by

  let n : ℕ :=
    articleRetainedCard T - blockLength + 1

  have hsum :
      (∑ s : Fin n,
        (A0
          - beta *
              consecutiveBlockSpan
                T s.1
                (by
                  have hs := s.2
                  dsimp [n] at hs
                  omega)
          - localErr))
        ≤
      ∑ s : Fin n,
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            dsimp [n] at hs
            omega) := by

    apply Finset.sum_le_sum
    intro s hs

    simpa [n] using hlocal s

  have hspan :
      articleConsecutiveSpanSum T
        =
      ∑ s : Fin n,
        consecutiveBlockSpan
          T s.1
          (by
            have hs := s.2
            dsimp [n] at hs
            omega) := by

    simpa [n] using
      articleConsecutiveSpanSum_eq_finSum T hS

  have hdef :
      articleConsecutiveBlockDefectSum T
        =
      ∑ s : Fin n,
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            dsimp [n] at hs
            omega) := by

    simp only [
      articleConsecutiveBlockDefectSum,
      dif_pos hS
    ]

    rfl

  have hcount :
      articleConsecutiveBlockCountR T = (n : ℝ) := by
    unfold articleConsecutiveBlockCountR slidingBlockCount
    simp only [n]

  rw [hspan, hdef, hcount]

  have hleft :
      (∑ s : Fin n,
        (A0
          - beta *
              consecutiveBlockSpan
                T s.1
                (by
                  have hs := s.2
                  dsimp [n] at hs
                  omega)
          - localErr))
        =
      A0 * (n : ℝ)
        - beta *
            (∑ s : Fin n,
              consecutiveBlockSpan
                T s.1
                (by
                  have hs := s.2
                  dsimp [n] at hs
                  omega))
        - (n : ℝ) * localErr := by

    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp [mul_comm]

  rw [← hleft]

  exact hsum

/--
Exact cancellation of the accumulated local error against the 262 shifted
decompositions.
-/
theorem blockLength_mul_articleAveragedBlockError
    (T localErr : ℝ) :
    (blockLength : ℝ) * articleAveragedBlockError T localErr
      =
    articleConsecutiveBlockCountR T * localErr := by

  unfold articleAveragedBlockError
  norm_num [blockLength]
  ring

/--
Finite shifted pinching derived directly from uniform stability of every
consecutive retained block.

This removes the global `hblocks` hypothesis from the finite article-level
theorem.  The only remaining finite hypothesis is the pointwise local
stability statement `hlocal`.
-/
theorem article_shifted_pinching_of_uniform_blocks
    (T localErr : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hlocal :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        A0
            - beta *
                consecutiveBlockSpan
                  T s.1
                  (by
                    have hs := s.2
                    omega)
            - localErr
          ≤
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            omega)) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T localErr
      ≤ articleStableDefect T := by

  apply
    article_shifted_pinching_finite
      T
      (articleAveragedBlockError T localErr)
      hS
      hT
      hl

  rw [blockLength_mul_articleAveragedBlockError]

  exact
    article_summed_uniform_block_stability
      T localErr hS hlocal

/-- Published-coefficient form of the same finite theorem. -/
theorem article_shifted_pinching_of_uniform_blocks_published
    (T localErr : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hlocal :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        A0
            - beta *
                consecutiveBlockSpan
                  T s.1
                  (by
                    have hs := s.2
                    omega)
            - localErr
          ≤
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            omega)) :
    (312 / 81875 : ℝ) * (articleRetainedCard T : ℝ)
      - (261 / 131000 : ℝ) * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T localErr
      ≤ articleStableDefect T := by

  simpa [alpha, pressureCost] using
    article_shifted_pinching_of_uniform_blocks
      T localErr hS hT hl hlocal

end HurtadoZeta23
