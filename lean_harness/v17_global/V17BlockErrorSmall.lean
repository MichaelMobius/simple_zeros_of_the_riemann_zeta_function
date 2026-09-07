import HurtadoZeta23.V17CompactOverlapCore
import HurtadoZeta23.ArticleBlockErrorSmall
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-- Number of complete consecutive length-450 retained blocks, as a real. -/
def v17ConsecutiveBlockCountR (T : ℝ) : ℝ :=
  ((articleRetainedCard T - 450 + 1 : ℕ) : ℝ)

/-- Exact local analytic loss in the v17 strong-block theorem. -/
def v17FinalLocalErr (T : ℝ) : ℝ :=
  404100 * v17ArticleCompactError T (articleTailMargin T)

/-- Exact accumulated error after division by the 450 shifted families. -/
def v17FinalBlockErr (T : ℝ) : ℝ :=
  v17ConsecutiveBlockCountR T * v17FinalLocalErr T / 450

/-- The lightweight v17 compact error is definitionally the same quantitative
error used in the historical asymptotic analysis. -/
theorem v17ArticleCompactError_eq_articleCompactError
    (T : ℝ) (M : ℕ) :
    v17ArticleCompactError T M = articleCompactError T M := by
  rfl

/-- The exact v17 local analytic loss tends to zero. -/
theorem tendsto_v17FinalLocalErr_zero :
    Tendsto v17FinalLocalErr atTop (𝓝 0) := by
  change
    Tendsto
      (fun T : ℝ =>
        404100 * articleCompactError T (articleTailMargin T))
      atTop (𝓝 0)
  simpa using
    tendsto_articleCompactError_margin_zero.const_mul 404100

/-- Equivalently, the local loss is `o(1)`. -/
theorem v17FinalLocalErr_isLittleO_one :
    v17FinalLocalErr =o[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  exact (isLittleO_one_iff ℝ).2 tendsto_v17FinalLocalErr_zero

/-- Globally the number of complete 450-block starts is at most the retained
cardinality plus one. -/
theorem v17ConsecutiveBlockCountR_le_retained_add_one
    (T : ℝ) :
    v17ConsecutiveBlockCountR T ≤ (articleRetainedCard T : ℝ) + 1 := by
  have hnat :
      articleRetainedCard T - 450 + 1 ≤ articleRetainedCard T + 1 := by
    omega
  unfold v17ConsecutiveBlockCountR
  exact_mod_cast hnat

/-- Hence the v17 block count is `O(globalN)`. -/
theorem v17ConsecutiveBlockCountR_isBigO_globalN :
    v17ConsecutiveBlockCountR =O[atTop] globalN := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_one_le_globalN] with T hN1
  have hcount0 : 0 ≤ v17ConsecutiveBlockCountR T := by
    unfold v17ConsecutiveBlockCountR
    positivity
  have hN0 : 0 ≤ globalN T := by
    unfold globalN
    positivity
  have hcountLe :
      v17ConsecutiveBlockCountR T ≤ globalN T + 1 := by
    have h1 := v17ConsecutiveBlockCountR_le_retained_add_one T
    have h2 := articleRetainedCard_cast_le_globalN T
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hcount0, abs_of_nonneg hN0]
  nlinarith

/-- The exact accumulated v17 Input-IV cost is negligible relative to the
dyadic zero count. -/
theorem v17FinalBlockErr_small :
    v17FinalBlockErr =o[atTop] globalN := by
  have hprod :
      (fun T : ℝ =>
        v17FinalLocalErr T * v17ConsecutiveBlockCountR T)
        =o[atTop] globalN := by
    have h :=
      v17FinalLocalErr_isLittleO_one.mul_isBigO
        v17ConsecutiveBlockCountR_isBigO_globalN
    simpa only [one_mul] using h
  have hscaled := hprod.const_mul_left ((450 : ℝ)⁻¹)
  refine hscaled.congr_left ?_
  intro T
  unfold v17FinalBlockErr
  rw [div_eq_mul_inv]
  ring

end HurtadoZeta23