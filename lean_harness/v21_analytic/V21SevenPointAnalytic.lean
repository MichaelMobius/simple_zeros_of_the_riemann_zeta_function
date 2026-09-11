import HurtadoZeta23.ExternalCertificateFrontier
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace HurtadoZeta23

/-- The literal seven-point functional, expanded into its 6 pressure terms and
21 kernel weights.  This is only a readable normal form for `localFp`; no new
mathematical assumption is introduced. -/
def v21ExplicitF (y : ℕ → ℝ) (s : ℕ) : ℝ :=
  pressure 0 * (y (s+1) - y s) +
  pressure 1 * (y (s+2) - y (s+1)) +
  pressure 2 * (y (s+3) - y (s+2)) +
  pressure 3 * (y (s+4) - y (s+3)) +
  pressure 4 * (y (s+5) - y (s+4)) +
  pressure 5 * (y (s+6) - y (s+5)) +
  (1/3 : ℝ) * (
    limitingWeight (y (s+1) - y s) +
    limitingWeight (y (s+2) - y (s+1)) +
    limitingWeight (y (s+3) - y (s+2)) +
    limitingWeight (y (s+4) - y (s+3)) +
    limitingWeight (y (s+5) - y (s+4)) +
    limitingWeight (y (s+6) - y (s+5))) +
  (2/5 : ℝ) * (
    limitingWeight (y (s+2) - y s) +
    limitingWeight (y (s+3) - y (s+1)) +
    limitingWeight (y (s+4) - y (s+2)) +
    limitingWeight (y (s+5) - y (s+3)) +
    limitingWeight (y (s+6) - y (s+4))) +
  (1/2 : ℝ) * (
    limitingWeight (y (s+3) - y s) +
    limitingWeight (y (s+4) - y (s+1)) +
    limitingWeight (y (s+5) - y (s+2)) +
    limitingWeight (y (s+6) - y (s+3))) +
  (2/3 : ℝ) * (
    limitingWeight (y (s+4) - y s) +
    limitingWeight (y (s+5) - y (s+1)) +
    limitingWeight (y (s+6) - y (s+2))) +
  limitingWeight (y (s+5) - y s) +
  limitingWeight (y (s+6) - y (s+1)) +
  2 * limitingWeight (y (s+6) - y s)

/-- The first and last three historical pressure coefficients each carry
exactly half of the total pressure mass. -/
lemma v21_pressure_half_masses :
    pressure 0 + pressure 1 + pressure 2 = (1/1000 : ℝ) ∧
    pressure 3 + pressure 4 + pressure 5 = (1/1000 : ℝ) := by
  constructor <;> simp [pressure] <;> norm_num

/-- Exact algebraic expansion of the historical seven-point functional. -/
theorem v21_localFp_eq_explicit (y : ℕ → ℝ) (s : ℕ) :
    localFp (limitingWeightOnPoints y) y s = v21ExplicitF y s := by
  simp only [localFp, localPressure, localPairEnergy, limitingWeightOnPoints,
    windowGap, v21ExplicitF]
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ]
  simp [pressure]
  ring

/-- The v21 target is exactly the historical external certificate frontier. -/
theorem v21_article_target_iff :
    ArchivedSevenPointClaim ↔ ArticleSevenPointInequality := by
  rfl

end HurtadoZeta23
