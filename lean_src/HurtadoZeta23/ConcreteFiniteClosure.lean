import HurtadoZeta23.ConcreteCompactOverlapInputIV
import HurtadoZeta23.ExternalCertificateFrontier
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# Finite-T closure at the two honest frontiers

This removes the per-block `hcert` hypothesis using the universal
seven-point statement and removes `hraw` using the compact-overlap chain.

The exact synthesis/finite-overlap identity is now proved in
`ArticleSynthesisOverlapClosed`, so the fully quantitative finite-T theorem
below constructs the uniform `hcompact` estimate internally from
`consecutiveGram_compact_quantitative`.

The only non-kernel trust frontier remaining here is the external universal
seven-point certificate statement.
-/

/--
Finite shifted pinching from one universal certificate and a uniform
compact-overlap estimate.
-/
theorem article_shifted_pinching_of_uniform_compact_and_certificate
    (hcertExt : ArchivedSevenPointClaim)
    (T eps : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 ≤ Zeta23.l T)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (heps : 0 ≤ eps)
    (hcompact :
      ∀ s : Fin (articleRetainedCard T - blockLength + 1),
        ∀ a b
          (ha : a < blockLength)
          (hb : b < blockLength),
          |(consecutiveGramBlock
              T
              s.1
              (by
                have hs := s.2
                omega)
              ⟨a, ha⟩
              ⟨b, hb⟩).re
              -
            limitingk
              (consecutiveY
                  T
                  s.1
                  (by
                    have hs := s.2
                    omega)
                  b
                -
               consecutiveY
                  T
                  s.1
                  (by
                    have hs := s.2
                    omega)
                  a)|
            ≤ eps) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError T (136764 * eps)
      ≤ articleStableDefect T := by

  have hL :
      0 ≤ articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hl

  exact
    article_shifted_pinching_of_uniform_compact_overlap
      T eps hS hT hl hPois hc heps
      (articleSevenPointCertificates_of_external hcertExt T hS hL)
      hcompact


/-- The scalar p=4 tail is nonnegative. -/
theorem p4Tail_nonneg_article
    (M : ℕ) :
    0 ≤ p4Tail M := by
  unfold p4Tail
  apply tsum_nonneg
  intro k
  unfold p4Majorant
  positivity

/-- The explicit quantitative Input-IV error is nonnegative in the
positive-height regime. -/
theorem articleCompactError_nonneg
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (M : ℕ) :
    0 ≤ articleCompactError T M := by

  have hL :
      0 < articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hl

  have hw :
      0 ≤ articleParams.w := by
    linarith [articleParams_valid.one_le_w]

  have hK :
      0 < limitingK 0 :=
    limitingK_zero_pos

  have hp4 :
      0 ≤ p4Tail M :=
    p4Tail_nonneg_article M

  have hraw :
      0 ≤ articleRawTailBound T M := by
    unfold articleRawTailBound
    positivity

  have hden :
      0 ≤
        |phiDMean
            articleParams.ϱ
            1
            (articleParams.L T)
            articleParams.w| *
          (articleParams.L T) ^ 2 := by
    positivity

  have hfirst :
      0 ≤
        articleRawTailBound T M /
          (|phiDMean
              articleParams.ϱ
              1
              (articleParams.L T)
              articleParams.w| *
            (articleParams.L T) ^ 2) :=
    div_nonneg hraw hden

  have hsecond :
      0 ≤
        20 *
            (articleParams.w / articleParams.L T) /
          limitingK 0 := by
    positivity

  unfold articleCompactError
  linarith

/--
Finite shifted pinching with the quantitative Input-IV estimate constructed
internally for every sliding block.

This is the finite-T theorem that no longer asks for either
`ArticleSynthesisOverlapIdentity` or a manually supplied `hcompact`.
-/
theorem article_shifted_pinching_of_quantitative_inputIV_and_certificate
    (hcertExt : ArchivedSevenPointClaim)
    (T : ℝ)
    (M : ℕ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hT : 0 ≤ T)
    (hl : 0 < Zeta23.l T)
    (hPois :
      Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (hwL :
      8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2)
    (hM1 : 1 ≤ M)
    (hM2 :
      (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk :
      (0 : ℤ) ≤ articleLastGridIndex T) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleAveragedBlockError
          T
          (136764 * articleCompactError T M)
      ≤ articleStableDefect T := by

  have heps :
      0 ≤ articleCompactError T M :=
    articleCompactError_nonneg hl M

  apply
    article_shifted_pinching_of_uniform_compact_and_certificate
      hcertExt
      T
      (articleCompactError T M)
      hS
      hT
      (le_of_lt hl)
      hPois
      hnorm
      heps

  intro s a b ha hb

  have hs :
      s.1 + blockLength ≤ articleRetainedCard T := by
    have hs0 := s.2
    omega

  have hq :=
    consecutiveGram_compact_quantitative
      hnorm
      hl
      hwL
      hsmall
      hM1
      hM2
      hkk
      s.1
      hs
      ⟨a, ha⟩
      ⟨b, hb⟩

  simpa only using hq

end HurtadoZeta23
