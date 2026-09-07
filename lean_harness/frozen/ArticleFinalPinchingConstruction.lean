import HurtadoZeta23.ArticleBlockErrorSmall
import HurtadoZeta23.ConcreteAsymptoticFrontier
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-!
# Construction of the final shifted-pinching input

All analytic Input-IV errors have now been closed.  This file assembles the
finite theorem into the exact `ArticleFinalPinchingInput` required by the
published asymptotic endgame.

The only remaining argument is `ArchivedSevenPointClaim`, which records the
external Arb/FLINT seven-point certificate.  No axiom is introduced here.
-/

/-- For sufficiently large positive height, the last finite critical-grid
index is nonnegative. -/
theorem articleLastGridIndex_nonneg_of_two_le_l
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T)
    (hTlarge : 2 * Real.pi ≤ T) :
    (0 : ℤ) ≤ articleLastGridIndex T := by

  have hL2 :
      2 ≤ articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hl2

  have hL0 :
      0 ≤ articleParams.L T := by
    linarith

  have hpi0 :
      0 < 2 * Real.pi := by
    positivity

  have hprod :
      2 * Real.pi
        ≤
      articleParams.L T * T := by

    have hmul :=
      mul_le_mul
        (show (1 : ℝ) ≤ articleParams.L T by linarith)
        hTlarge
        (le_of_lt hpi0)
        hL0

    simpa using hmul

  have hx1 :
      (1 : ℝ)
        ≤
      articleParams.L T * T / (2 * Real.pi) := by

    exact
      (le_div_iff₀ hpi0).2
        (by simpa using hprod)

  have hfloor :
      articleParams.L T * T / (2 * Real.pi) - 1
        <
      (articleParams.d T : ℝ) := by

    unfold Zeta23.Params.d

    simpa using
      (Nat.sub_one_lt_floor
        (articleParams.L T * T / (2 * Real.pi)))

  have hdcast :
      (0 : ℝ) < (articleParams.d T : ℝ) := by
    exact
      lt_of_le_of_lt
        (sub_nonneg.mpr hx1)
        hfloor

  have hdpos :
      0 < articleParams.d T := by
    exact_mod_cast hdcast

  have hd1 :
      1 ≤ articleParams.d T := by
    omega

  have hd1z :
      (1 : ℤ) ≤ (articleParams.d T : ℤ) := by
    exact_mod_cast hd1

  unfold articleLastGridIndex
  exact sub_nonneg.mpr hd1z

/-- Positivity of the exact finite simple-synthesis normalization in the
large-height compact-overlap regime. -/
theorem articleNormalization_pos
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (hwL :
      8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T
        ≤ limitingK 0 / 2) :
    0 <
      (articleParams.atD T).a T *
        (articleParams.atD T).L T ^ 2 := by

  have hK :
      0 < limitingK 0 :=
    limitingK_zero_pos

  have hclose0 :=
    phiDMean_close_limitingK_zero
      articleParams_valid.taper
      articleParams_valid.one_le_w
      hwL

  have hclose :
      |phiDMean
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w
        - limitingK 0|
        ≤ limitingK 0 / 2 :=
    hclose0.trans hsmall

  have hlower :=
    (abs_le.mp hclose).1

  have hmean :
      0 <
        phiDMean
          articleParams.ϱ
          1
          (articleParams.L T)
          articleParams.w := by
    linarith

  have ha :
      0 < (articleParams.atD T).a T := by
    rw [article_atD_a_eq_phiDMean]
    exact hmean

  have hL :
      0 < (articleParams.atD T).L T := by
    simp only [Zeta23.Params.atD_L]
    simpa [articleParams_L_eq_zeta_l] using hl

  exact
    mul_pos ha (pow_pos hL 2)

/-- If there are fewer than 262 retained columns, the endpoint correction
already dominates the positive retained-cardinality term. -/
theorem article_pinching_of_too_few_retained
    (T : ℝ)
    (hT : 0 ≤ T)
    (hl : 0 < Zeta23.l T)
    (hS : ¬ blockLength ≤ articleRetainedCard T) :
    alpha * (articleRetainedCard T : ℝ)
      - pressureCost * samplingSpanScale T
      - endpointCorrection
      - articleFinalBlockErr T
      ≤ articleStableDefect T := by

  have hretNat :
      articleRetainedCard T ≤ blockLength - 1 := by
    omega

  have hret :
      (articleRetainedCard T : ℝ)
        ≤
      ((blockLength - 1 : ℕ) : ℝ) := by
    exact_mod_cast hretNat

  have hA0 :
      0 ≤ A0 := by
    rw [A0_eq]
    norm_num

  have hm :
      0 < (blockLength : ℝ) := by
    norm_num [blockLength]

  have hmul :
      A0 * (articleRetainedCard T : ℝ)
        ≤
      A0 * ((blockLength - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hret hA0

  have hdiv :
      A0 * (articleRetainedCard T : ℝ) / blockLength
        ≤
      A0 * ((blockLength - 1 : ℕ) : ℝ) / blockLength :=
    div_le_div_of_nonneg_right hmul (le_of_lt hm)

  have hendpoint :
      alpha * (articleRetainedCard T : ℝ)
        ≤ endpointCorrection := by

    rw [alpha_eq_A0_div_m]
    unfold endpointCorrection

    calc
      (A0 / (blockLength : ℝ)) *
          (articleRetainedCard T : ℝ)
          =
        A0 * (articleRetainedCard T : ℝ) /
          blockLength := by
            ring

      _ ≤
        A0 * ((blockLength - 1 : ℕ) : ℝ) /
          blockLength := hdiv

  have hspan :
      0 ≤ samplingSpanScale T :=
    samplingSpanScale_nonneg T hT (le_of_lt hl)

  have hp :
      0 ≤ pressureCost := by
    norm_num [pressureCost]

  have hcompact :
      0 ≤
        articleCompactError
          T
          (articleTailMargin T) :=
    articleCompactError_nonneg
      hl
      (articleTailMargin T)

  have hlocal :
      0 ≤ articleFinalLocalErr T := by
    unfold articleFinalLocalErr
    exact mul_nonneg (by norm_num) hcompact

  have hcount :
      0 ≤ articleConsecutiveBlockCountR T := by
    have hnat :
        0 ≤
          slidingBlockCount
            (articleRetainedCard T)
            blockLength :=
      Nat.zero_le _
    unfold articleConsecutiveBlockCountR
    exact_mod_cast hnat

  have hblock :
      0 ≤ articleFinalBlockErr T := by
    unfold articleFinalBlockErr
    unfold articleAveragedBlockError
    exact
      div_nonneg
        (mul_nonneg hcount hlocal)
        (by positivity)

  have hdef :
      0 ≤ articleStableDefect T := by
    unfold articleStableDefect
    exact gramSpectralDefect_nonneg _ _

  nlinarith [mul_nonneg hp hspan]

/--
The final asymptotic pinching package, conditional only on the archived
seven-point certificate statement.
-/
noncomputable def articleFinalPinchingInput_of_certificate
    (hcertExt : ArchivedSevenPointClaim) :
    ArticleFinalPinchingInput := by

  refine
    {
      blockErr := articleFinalBlockErr
      blockErr_small := articleFinalBlockErr_small
      pinching_eventually := ?_
    }

  filter_upwards
    [eventually_two_le_zeta_l,
     eventually_article_hwL,
     eventually_article_hsmall,
     eventually_one_le_articleTailMargin,
     eventually_articleTailMargin_add_two_le_sq,
     eventually_ge_atTop (2 * Real.pi),
     Zeta23.ThmD.eventually_w8 articleParams_valid]
    with T hl2 hwL hsmall hM1 hM2 hTlarge h8

  have hl :
      0 < Zeta23.l T := by
    linarith

  have hT :
      0 ≤ T := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith

  by_cases hS :
      blockLength ≤ articleRetainedCard T

  ·
    have hPois :
        Zeta23.ZeroSide.PoissonSq
          T
          (articleParams.atD T) :=
      Zeta23.ThmD.poissonSqD
        articleParams_valid
        h8

    have hnorm :
        0 <
          (articleParams.atD T).a T *
            (articleParams.atD T).L T ^ 2 :=
      articleNormalization_pos
        hl hwL hsmall

    have hkk :
        (0 : ℤ) ≤ articleLastGridIndex T :=
      articleLastGridIndex_nonneg_of_two_le_l
        hl2 hTlarge

    have hfin :=
      article_shifted_pinching_of_quantitative_inputIV_and_certificate
        hcertExt
        T
        (articleTailMargin T)
        hS
        hT
        hl
        hPois
        hnorm
        hwL
        hsmall
        hM1
        hM2
        hkk

    simpa [articleFinalBlockErr, articleFinalLocalErr] using hfin

  ·
    exact
      article_pinching_of_too_few_retained
        T hT hl hS

end HurtadoZeta23