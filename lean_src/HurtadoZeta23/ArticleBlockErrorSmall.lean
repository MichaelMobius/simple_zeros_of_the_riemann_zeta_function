import HurtadoZeta23.ArticleCompactErrorLimit
import HurtadoZeta23.RetainedCardinalityBridge
import HurtadoZeta23.UniformBlockAssembly
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-!
# The accumulated block error is o(N)

The local quantitative Input-IV error tends to zero.  The number of sliding
blocks is at most the retained cardinality, and the retained set is a subset
of the dyadic zero set counted by `Ndist`, hence by `Ncount`.

Therefore

  (#blocks) * o(1) / 262 = o(globalN).
-/

/-- The local error inserted into the finite shifted-pinching theorem. -/
def articleFinalLocalErr (T : ℝ) : ℝ :=
  136764 *
    articleCompactError T (articleTailMargin T)

/-- The accumulated error after averaging over the 262 shifted decompositions. -/
def articleFinalBlockErr (T : ℝ) : ℝ :=
  articleAveragedBlockError T (articleFinalLocalErr T)

/-- The retained finite Gram cardinality is bounded by the full dyadic
zero count with multiplicity. -/
theorem articleRetainedCard_le_Ncount
    (T : ℝ) :
    articleRetainedCard T
      ≤
    Zeta23.Ncount T (2 * T) := by

  rw [articleRetainedCard_eq_ncard]

  have hsub :
      retainedSimpleCriticalSet T
        ⊆
      Zeta23.zerosIn T (2 * T) := by
    intro ρ hρ
    exact hρ.1.1.1

  have hncard :
      (retainedSimpleCriticalSet T).ncard
        ≤
      (Zeta23.zerosIn T (2 * T)).ncard :=
    Set.ncard_le_ncard
      hsub
      (Zeta23.zerosIn_finite T (2 * T))

  calc
    (retainedSimpleCriticalSet T).ncard
        ≤
      (Zeta23.zerosIn T (2 * T)).ncard :=
        hncard

    _ =
      Zeta23.Ndist T (2 * T) := by
        rfl

    _ ≤
      Zeta23.Ncount T (2 * T) :=
        (Zeta23.trivial_chain₀ T (2 * T)).2.2.2.2.2

/-- Real-valued retained-cardinality bound in final-assembly notation. -/
theorem articleRetainedCard_cast_le_globalN
    (T : ℝ) :
    (articleRetainedCard T : ℝ)
      ≤
    globalN T := by

  unfold globalN
  exact_mod_cast articleRetainedCard_le_Ncount T

/-- Globally, the number of full sliding-block starts is at most the retained
cardinality plus one.  The `+1` is necessary at very small heights because
`slidingBlockCount S m = S - m + 1` evaluates to `1` when `S < m`. -/
theorem articleConsecutiveBlockCountR_le_retained_add_one
    (T : ℝ) :
    articleConsecutiveBlockCountR T
      ≤
    (articleRetainedCard T : ℝ) + 1 := by

  have hnat :
      slidingBlockCount
          (articleRetainedCard T)
          blockLength
        ≤
      articleRetainedCard T + 1 := by
    unfold slidingBlockCount
    omega

  unfold articleConsecutiveBlockCountR
  exact_mod_cast hnat

/-- Hence the block count is globally bounded by `globalN + 1`. -/
theorem articleConsecutiveBlockCountR_le_globalN_add_one
    (T : ℝ) :
    articleConsecutiveBlockCountR T
      ≤
    globalN T + 1 := by

  have h1 :=
    articleConsecutiveBlockCountR_le_retained_add_one T

  have h2 :=
    articleRetainedCard_cast_le_globalN T

  linarith

/-- Eventually the dyadic zero count is at least one. -/
theorem eventually_one_le_globalN :
    ∀ᶠ T : ℝ in atTop,
      (1 : ℝ) ≤ globalN T := by

  have h :=
    zetaDyadicN_tendsto_atTop.eventually_ge_atTop (1 : ℝ)

  simpa [zetaDyadicN, globalN] using h

/-- The sliding-block count is `O(globalN)`. -/
theorem articleConsecutiveBlockCountR_isBigO_globalN :
    articleConsecutiveBlockCountR
      =O[atTop]
    globalN := by

  refine IsBigO.of_bound 2 ?_

  filter_upwards [eventually_one_le_globalN] with T hN1

  have hcount0 :
      0 ≤ articleConsecutiveBlockCountR T := by
    unfold articleConsecutiveBlockCountR
    positivity

  have hN0 :
      0 ≤ globalN T := by
    linarith

  have hcountLe :
      articleConsecutiveBlockCountR T
        ≤
      globalN T + 1 :=
    articleConsecutiveBlockCountR_le_globalN_add_one T

  rw [
    Real.norm_eq_abs,
    Real.norm_eq_abs,
    abs_of_nonneg hcount0,
    abs_of_nonneg hN0
  ]

  nlinarith

/-- The local finite-block error tends to zero. -/
theorem tendsto_articleFinalLocalErr_zero :
    Tendsto articleFinalLocalErr atTop (𝓝 0) := by

  change
    Tendsto
      (fun T : ℝ =>
        136764 *
          articleCompactError T (articleTailMargin T))
      atTop
      (𝓝 0)

  simpa using
    tendsto_articleCompactError_margin_zero.const_mul
      136764

/-- The local error is `o(1)`. -/
theorem articleFinalLocalErr_isLittleO_one :
    articleFinalLocalErr
      =o[atTop]
    (fun _ : ℝ => (1 : ℝ)) := by

  exact
    (isLittleO_one_iff ℝ).2
      tendsto_articleFinalLocalErr_zero

/--
The averaged accumulated Input-IV cost is negligible relative to the dyadic
zero count.
-/
theorem articleFinalBlockErr_small :
    articleFinalBlockErr
      =o[atTop]
    globalN := by

  have hprod :
      (fun T : ℝ =>
        articleFinalLocalErr T *
          articleConsecutiveBlockCountR T)
        =o[atTop]
      (fun T : ℝ => globalN T) := by

    have h :=
      articleFinalLocalErr_isLittleO_one.mul_isBigO
        articleConsecutiveBlockCountR_isBigO_globalN

    simpa only [one_mul] using h

  have hscaled :=
    hprod.const_mul_left
      ((blockLength : ℝ)⁻¹)

  refine hscaled.congr_left ?_

  intro T

  unfold articleFinalBlockErr
  unfold articleAveragedBlockError

  rw [div_eq_mul_inv]
  ring

end HurtadoZeta23