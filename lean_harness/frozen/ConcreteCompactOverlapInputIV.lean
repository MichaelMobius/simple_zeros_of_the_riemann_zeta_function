import HurtadoZeta23.ArticleSynthesisOverlapClosed
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-!
# Quantitative Input IV for one retained block

This file combines the already formalized p=4 finite-grid tail with
`compactOverlap_quantitative` and transfers the result to the actual Gram
entry using the now-proved exact synthesis/finite-overlap identity.

There is no longer an `ArticleSynthesisOverlapIdentity` hypothesis in this
quantitative Input-IV theorem.
-/

/-- Explicit raw two-sided p=4 tail majorant for the article window. -/
def articleRawTailBound (T : ℝ) (M : ℕ) : ℝ :=
  2 *
    ((((Zeta23.ThmD.cDT articleParams.ϱ 1) / articleParams.w) ^ 2 /
        (articleCriticalStep T) ^ 4) *
      p4Tail M)

/-- Explicit normalized compact-overlap error obtained from Input IV. -/
def articleCompactError (T : ℝ) (M : ℕ) : ℝ :=
  articleRawTailBound T M /
      (|phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w| *
        (articleParams.L T) ^ 2)
    +
  20 * (articleParams.w / articleParams.L T) / limitingK 0

/--
Quantitative compact overlap for two actual positions in a retained block.

`M+2 <= l(T)^2` is the conservative endpoint margin proved by the discrete
centrality bridge.
-/
theorem consecutiveGram_compact_quantitative
    {T : ℝ}
    (hnorm :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 :
      (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk :
      (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    |(consecutiveGramBlock T s hs i j).re -
        limitingk
          (consecutiveY T s hs j.1 -
            consecutiveY T s hs i.1)|
      ≤
    articleCompactError T M := by

  have hcent :=
    consecutiveZero_pair_articleGridCentrality
      hl s hs j i hM2

  have htail :
      |intervalFiniteGridOverlap
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w
          T
          (consecutiveZero T s hs j).im
          (consecutiveZero T s hs i).im
          0
          (articleLastGridIndex T)
        -
        fullGridOverlap
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w
          (consecutiveZero T s hs j).im
          (consecutiveZero T s hs i).im|
        ≤ articleRawTailBound T M := by

    have h :=
      intervalFiniteGridOverlap_error_le_p4
        (ϱ := articleParams.ϱ)
        (lam := 1)
        (L := articleParams.L T)
        (w := articleParams.w)
        (T := T)
        (τ := (consecutiveZero T s hs j).im)
        (τ' := (consecutiveZero T s hs i).im)
        (kMin := 0)
        (kMax := articleLastGridIndex T)
        (M := M)
        articleParams_valid.taper
        one_pos
        le_rfl
        articleParams_valid.one_le_w
        hwL
        hkk
        hM1
        (by
          simpa [articleCriticalStep] using hcent.1)
        (by
          simpa [articleCriticalStep] using hcent.2)

    simpa [articleRawTailBound, articleCriticalStep] using h

  have hquant :=
    compactOverlap_quantitative
      (ϱ := articleParams.ϱ)
      (L := articleParams.L T)
      (w := articleParams.w)
      (T := T)
      (τ := (consecutiveZero T s hs j).im)
      (τ' := (consecutiveZero T s hs i).im)
      (tailErr := articleRawTailBound T M)
      (kMin := 0)
      (kMax := articleLastGridIndex T)
      articleParams_valid.taper
      articleParams_valid.one_le_w
      hwL
      hsmall
      htail

  rw [
    consecutiveGramBlock_re_eq_normalizedIntervalOverlap_rev
      hnorm s hs i j
  ]

  rw [
    consecutiveY_sub_eq_scaled_im_sub
      T s hs i j
  ]

  simpa [articleCompactError] using hquant

end HurtadoZeta23
