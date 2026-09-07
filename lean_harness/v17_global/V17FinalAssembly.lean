import HurtadoZeta23.V17ConcreteShiftedAssembly450
import HurtadoZeta23.V17BlockErrorSmall
import HurtadoZeta23.ConcreteRetainedCore
import HurtadoZeta23.ConcreteStableSeam
import HurtadoZeta23.RvMAsymptotics
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-- Large-height nonnegativity of the last finite critical-grid index, stated
locally for the v17 closure so the new proof does not depend on the historical
262-point final wrapper. -/
theorem v17_articleLastGridIndex_nonneg_of_two_le_l
    {T : ℝ}
    (hl2 : 2 ≤ Zeta23.l T)
    (hTlarge : 2 * Real.pi ≤ T) :
    (0 : ℤ) ≤ articleLastGridIndex T := by
  have hL2 : 2 ≤ articleParams.L T := by
    simpa [articleParams_L_eq_zeta_l] using hl2
  have hL0 : 0 ≤ articleParams.L T := by linarith
  have hpi0 : 0 < 2 * Real.pi := by positivity
  have hprod : 2 * Real.pi ≤ articleParams.L T * T := by
    have hmul :=
      mul_le_mul
        (show (1 : ℝ) ≤ articleParams.L T by linarith)
        hTlarge (le_of_lt hpi0) hL0
    simpa using hmul
  have hx1 :
      (1 : ℝ) ≤ articleParams.L T * T / (2 * Real.pi) :=
    (le_div_iff₀ hpi0).2 (by simpa using hprod)
  have hfloor :
      articleParams.L T * T / (2 * Real.pi) - 1 <
        (articleParams.d T : ℝ) := by
    unfold Zeta23.Params.d
    simpa using
      (Nat.sub_one_lt_floor
        (articleParams.L T * T / (2 * Real.pi)))
  have hdcast : (0 : ℝ) < (articleParams.d T : ℝ) :=
    lt_of_le_of_lt (sub_nonneg.mpr hx1) hfloor
  have hdpos : 0 < articleParams.d T := by exact_mod_cast hdcast
  have hd1 : 1 ≤ articleParams.d T := by omega
  have hd1z : (1 : ℤ) ≤ (articleParams.d T : ℤ) := by
    exact_mod_cast hd1
  unfold articleLastGridIndex
  exact sub_nonneg.mpr hd1z

/-- Positivity of the exact finite simple-synthesis normalization in the v17
large-height compact-overlap regime. -/
theorem v17_articleNormalization_pos
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall :
      4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2) :
    0 < (articleParams.atD T).a T *
      (articleParams.atD T).L T ^ 2 := by
  have hK : 0 < limitingK 0 := limitingK_zero_pos
  have hclose0 :=
    phiDMean_close_limitingK_zero
      articleParams_valid.taper
      articleParams_valid.one_le_w hwL
  have hclose :
      |phiDMean articleParams.ϱ 1 (articleParams.L T) articleParams.w -
          limitingK 0| ≤ limitingK 0 / 2 :=
    hclose0.trans hsmall
  have hlower := (abs_le.mp hclose).1
  have hmean :
      0 < phiDMean
        articleParams.ϱ 1 (articleParams.L T) articleParams.w := by
    linarith
  have ha : 0 < (articleParams.atD T).a T := by
    rw [article_atD_a_eq_phiDMean]
    exact hmean
  have hL : 0 < (articleParams.atD T).L T := by
    simp only [Zeta23.Params.atD_L]
    simpa [articleParams_L_eq_zeta_l] using hl
  exact mul_pos ha (pow_pos hL 2)

/-- Complete v17 pinching error after replacing retained cardinality and span
by the global zero-count quantities. -/
def v17PinchingError (T : ℝ) : ℝ :=
  v17Alpha * interiorBoundaryLoss T
    + v17PressureCost * articleRvMSpanInputs.totalErr T
    + v17EndpointCorrection
    + v17FinalBlockErr T

/-- The finite shifted-pinching inequality holds eventually, conditional only
on the two explicit external certificate frontiers.  The small-cardinality
case is absorbed by the endpoint correction. -/
theorem v17_pinching_eventually_of_claims
    (hcertExt : ArchivedSevenPointClaim)
    (hscalarExt : V17ScalarPressureClaim) :
    ∀ᶠ T in atTop,
      v17Alpha * (articleRetainedCard T : ℝ)
        - v17PressureCost * samplingSpanScale T
        - v17EndpointCorrection
        - v17FinalBlockErr T
        ≤ articleStableDefect T := by
  filter_upwards
    [eventually_two_le_zeta_l,
     eventually_article_hwL,
     eventually_article_hsmall,
     eventually_one_le_articleTailMargin,
     eventually_articleTailMargin_add_two_le_sq,
     eventually_ge_atTop (2 * Real.pi),
     Zeta23.ThmD.eventually_w8 articleParams_valid]
    with T hl2 hwL hsmall hM1 hM2 hTlarge h8

  have hl : 0 < Zeta23.l T := by linarith
  have hT : 0 ≤ T := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith

  by_cases hS : 450 ≤ articleRetainedCard T
  · have hPois :
        Zeta23.ZeroSide.PoissonSq T (articleParams.atD T) :=
      Zeta23.ThmD.poissonSqD articleParams_valid h8
    have hnorm :
        0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2 :=
      v17_articleNormalization_pos hl hwL hsmall
    have hkk : (0 : ℤ) ≤ articleLastGridIndex T :=
      v17_articleLastGridIndex_nonneg_of_two_le_l hl2 hTlarge
    have hfin :=
      v17_concrete_shifted_assembly_450
        hcertExt hscalarExt hS hT hPois hnorm hl hwL hsmall
        hM1 hM2 hkk
    simpa [v17FinalBlockErr, v17FinalLocalErr,
      v17ConsecutiveBlockCountR] using hfin

  · have hretNat : articleRetainedCard T ≤ 449 := by omega
    have hret : (articleRetainedCard T : ℝ) ≤ 449 := by
      exact_mod_cast hretNat
    have halpha : 0 ≤ v17Alpha := by norm_num [v17Alpha]
    have hendEq : v17EndpointCorrection = v17Alpha * 449 := by
      norm_num [v17EndpointCorrection, v17Alpha, v17A]
    have hend :
        v17Alpha * (articleRetainedCard T : ℝ) ≤ v17EndpointCorrection := by
      rw [hendEq]
      exact mul_le_mul_of_nonneg_left hret halpha
    have hspan : 0 ≤ samplingSpanScale T :=
      samplingSpanScale_nonneg T hT (le_of_lt hl)
    have hp : 0 ≤ v17PressureCost := by
      norm_num [v17PressureCost]
    have heps :
        0 ≤ v17ArticleCompactError T (articleTailMargin T) :=
      v17ArticleCompactError_nonneg hl (articleTailMargin T)
    have hlocal : 0 ≤ v17FinalLocalErr T := by
      unfold v17FinalLocalErr
      exact mul_nonneg (by norm_num) heps
    have hcount : 0 ≤ v17ConsecutiveBlockCountR T := by
      unfold v17ConsecutiveBlockCountR
      positivity
    have hblock : 0 ≤ v17FinalBlockErr T := by
      unfold v17FinalBlockErr
      positivity
    have hdef : 0 ≤ articleStableDefect T := by
      unfold articleStableDefect
      exact gramSpectralDefect_nonneg _ _
    nlinarith [mul_nonneg hp hspan]

/-- The complete v17 pinching error is `o(N(T,2T))`. -/
theorem v17PinchingError_small :
    v17PinchingError =o[atTop] globalN := by
  have hret0 := interiorBoundaryLocalCount_proved.loss_small_zetaDyadicN
  have hretBase : interiorBoundaryLoss =o[atTop] globalN := by
    change interiorBoundaryLoss =o[atTop] zetaDyadicN
    exact hret0
  have hret :
      (fun T : ℝ => v17Alpha * interiorBoundaryLoss T)
        =o[atTop] globalN :=
    hretBase.const_mul_left v17Alpha

  have hspan0 : articleRvMSpanInputs.totalErr =o[atTop] zetaDyadicN :=
    isLittleO_zetaDyadicN_of_isLittleO_TlogT
      articleRvMSpanInputs_totalErr_small
  have hspanBase : articleRvMSpanInputs.totalErr =o[atTop] globalN := by
    change articleRvMSpanInputs.totalErr =o[atTop] zetaDyadicN
    exact hspan0
  have hspan :
      (fun T : ℝ => v17PressureCost * articleRvMSpanInputs.totalErr T)
        =o[atTop] globalN :=
    hspanBase.const_mul_left v17PressureCost

  have hend0 := const_isLittleO_zetaDyadicN v17EndpointCorrection
  have hend :
      (fun _ : ℝ => v17EndpointCorrection) =o[atTop] globalN := by
    change (fun _ : ℝ => v17EndpointCorrection) =o[atTop] zetaDyadicN
    exact hend0

  unfold v17PinchingError
  exact ((hret.add hspan).add hend).add v17FinalBlockErr_small

/-- The finite v17 pinching estimate implies the global defect lower bound
`D ≥ alpha*S - pressureCost*N - o(N)`. -/
theorem v17_defect_global_from_claims
    (hcertExt : ArchivedSevenPointClaim)
    (hscalarExt : V17ScalarPressureClaim) :
    ∀ᶠ T in atTop,
      v17Alpha * globalS T
        - v17PressureCost * globalN T
        - v17PinchingError T
        ≤ articleStableDefect T := by
  have ha : 0 ≤ v17Alpha := by norm_num [v17Alpha]
  have hp : 0 ≤ v17PressureCost := by norm_num [v17PressureCost]
  filter_upwards
    [articleCentralRetentionCounts.eventually_retained_bound,
     articleRvMSpanInputs.eventually_span_bound,
     v17_pinching_eventually_of_claims hcertExt hscalarExt]
    with T hret hspan hpinch
  have hret' :
      v17Alpha * (globalS T - interiorBoundaryLoss T)
        ≤ v17Alpha * (articleRetainedCard T : ℝ) := by
    rw [articleRetainedCard_cast_eq_retainedReal T]
    exact mul_le_mul_of_nonneg_left hret ha
  have hspan' :
      v17PressureCost * samplingSpanScale T
        ≤ v17PressureCost *
          (globalN T + articleRvMSpanInputs.totalErr T) :=
    mul_le_mul_of_nonneg_left hspan hp
  unfold v17PinchingError
  linarith

/-- Conditional end-to-end v17 global refinement.  All internal analytic,
Gram, spectral, shifted-pressure, and asymptotic steps are kernel-checked;
only `ArchivedSevenPointClaim` and `V17ScalarPressureClaim` remain explicit
external trust inputs. -/
noncomputable def v17GlobalRefinement_of_claims
    (hcertExt : ArchivedSevenPointClaim)
    (hscalarExt : V17ScalarPressureClaim) :
    V17GlobalRefinement := by
  refine
    { err := fun T => articleBaselineWithDefect.err T + v17PinchingError T
      err_small := ?_
      bound := ?_ }
  · change
      (fun T => articleBaselineWithDefect.err T + v17PinchingError T)
        =o[atTop] globalN
    exact articleBaselineWithDefect.err_small.add v17PinchingError_small
  · have hbase := articleBaselineWithDefect.bound
    have hdef := v17_defect_global_from_claims hcertExt hscalarExt
    filter_upwards [hbase, hdef] with T hb hd
    change
      HMT * globalN T + v17Alpha * globalS T
        - v17PressureCost * globalN T
        - (articleBaselineWithDefect.err T + v17PinchingError T)
        ≤ globalS T
    linarith

/-- Final published epsilon theorem, conditional exactly on the two explicit
certificate frontiers. -/
theorem v17_published_eps_form_of_claims
    (hcertExt : ArchivedSevenPointClaim)
    (hscalarExt : V17ScalarPressureClaim) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (v17PublishedConstant - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  exact v17_published_eps_form_from_global_refinement
    (v17GlobalRefinement_of_claims hcertExt hscalarExt)

end HurtadoZeta23