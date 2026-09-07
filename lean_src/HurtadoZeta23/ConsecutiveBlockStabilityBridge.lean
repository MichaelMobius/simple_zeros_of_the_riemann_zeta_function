import HurtadoZeta23.UniformBlockAssembly
import HurtadoZeta23.PoissonGaborBridge
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Consecutive block stability bridge

This file connects the abstract 262-point stability theorem to one *actual*
consecutive retained Gram block.

It deliberately exposes the three local interfaces that still have to be
closed independently:

1. the seven-point certificate for the normalized ordinates;
2. the compact-overlap approximation for the actual block overlaps;
3. the matrix Block-defect inequality for the actual Gram block.

Once those are supplied, all order/span bookkeeping and the passage from the
raw overlap error to the block defect are automatic.
-/

/--
One actual consecutive retained block satisfies the manuscript's uniform
stability inequality as soon as the certificate, raw overlap approximation,
Block-defect inequality, and off-diagonal-energy identification are supplied.
-/
theorem consecutiveBlock_stability_of_raw_overlap
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (hL : 0 ≤ articleParams.L T)
    (overlap : ℕ → ℕ → ℝ)
    (eps : ℝ)
    (hcert :
      SevenPointCertificate
        (limitingWeightOnPoints (consecutiveY T s hs))
        (consecutiveY T s hs)
        blockLength)
    (hraw :
      RawPointwiseOverlapApproximation262
        (consecutiveY T s hs)
        overlap
        eps)
    (hblock :
      min 1 (offDiagonalEnergy (consecutiveGramBlock T s hs))
        ≤ consecutiveBlockDefect T s hs)
    (hGram :
      globalPairEnergyNat blockLength
          (fun a b => overlap a b ^ 2)
        =
      offDiagonalEnergy (consecutiveGramBlock T s hs)) :
    A0
        - beta * consecutiveBlockSpan T s hs
        - 136764 * eps
      ≤
    consecutiveBlockDefect T s hs := by

  have hbase :=
    block_stability_262_of_raw_overlap
      (consecutiveY T s hs)
      overlap
      hcert
      (consecutiveY_mono T s hs hL)
      (consecutiveBlockSpan_nonneg T s hs hL)
      (consecutiveBlockDefect_nonneg T s hs)
      hblock
      hraw
      hGram

  unfold consecutiveBlockSpan

  linarith

/--
Uniform raw-overlap control for every actual consecutive retained block feeds
directly into the shifted-pinching theorem.

The accumulated local error is exactly the averaged error already formalized
in `UniformBlockAssembly`, with per-block error `136764 * eps`.
-/
theorem article_shifted_pinching_of_uniform_raw_overlap
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (overlap :
      Fin (articleRetainedCard T - blockLength + 1) →
        ℕ → ℕ → ℝ)
    (hcert :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        SevenPointCertificate
          (limitingWeightOnPoints
            (consecutiveY
              T s.1
              (by
                have hs := s.2
                omega)))
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          blockLength)
    (hraw :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        RawPointwiseOverlapApproximation262
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          (overlap s)
          eps)
    (hblock :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        min 1
            (offDiagonalEnergy
              (consecutiveGramBlock
                T s.1
                (by
                  have hs := s.2
                  omega)))
          ≤
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            omega))
    (hGram :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        globalPairEnergyNat blockLength
            (fun a b => overlap s a b ^ 2)
          =
        offDiagonalEnergy
          (consecutiveGramBlock
            T s.1
            (by
              have hs := s.2
              omega))) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  have hL :
      0 ≤ articleParams.L T := by
    rw [articleParams_L_eq_zeta_l]
    exact hl

  apply
    article_shifted_pinching_of_uniform_blocks
      T
      (136764 * eps)
      hS
      hT
      hl

  intro s

  have hfit :
      s.1 + blockLength ≤ articleRetainedCard T := by
    have hslt := s.2
    omega

  exact
    consecutiveBlock_stability_of_raw_overlap
      T
      s.1
      hfit
      hL
      (overlap s)
      eps
      (hcert s)
      (hraw s)
      (hblock s)
      (hGram s)

/-- Published-coefficient version of the same uniform raw-overlap theorem. -/
theorem article_shifted_pinching_of_uniform_raw_overlap_published
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (overlap :
      Fin (articleRetainedCard T - blockLength + 1) →
        ℕ → ℕ → ℝ)
    (hcert :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        SevenPointCertificate
          (limitingWeightOnPoints
            (consecutiveY
              T s.1
              (by
                have hs := s.2
                omega)))
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          blockLength)
    (hraw :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        RawPointwiseOverlapApproximation262
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega))
          (overlap s)
          eps)
    (hblock :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        min 1
            (offDiagonalEnergy
              (consecutiveGramBlock
                T s.1
                (by
                  have hs := s.2
                  omega)))
          ≤
        consecutiveBlockDefect
          T s.1
          (by
            have hs := s.2
            omega))
    (hGram :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        globalPairEnergyNat blockLength
            (fun a b => overlap s a b ^ 2)
          =
        offDiagonalEnergy
          (consecutiveGramBlock
            T s.1
            (by
              have hs := s.2
              omega))) :
    (312 / 81875 : ℝ) * (articleRetainedCard T : ℝ)
      - (261 / 131000 : ℝ) * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤
    articleStableDefect T := by

  simpa [alpha, pressureCost] using
    article_shifted_pinching_of_uniform_raw_overlap
      T eps hS hT hl overlap hcert hraw hblock hGram

end HurtadoZeta23
