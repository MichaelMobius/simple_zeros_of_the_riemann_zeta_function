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

/-- Every historical pressure coefficient is at least the endpoint value
`2714 / 10^7`. -/
lemma v21_pressure_min (j : Fin 6) :
    (2714 / 10000000 : ℝ) ≤ pressure j := by
  fin_cases j <;> norm_num [pressure]

/-- The pressure cutoff used by the historical Arb verifier has the exact
positive margin `9 / 500000000` above `delta`. -/
lemma v21_pressure_cutoff_margin :
    (2714 / 10000000 : ℝ) * (1437 / 100 : ℝ) - delta
      = (9 / 500000000 : ℝ) := by
  norm_num [delta]

/-- Replacing every position-dependent pressure coefficient by its minimum
can only decrease the pressure on six nonnegative gaps. -/
lemma v21_pressure_floor_six
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) (h2 : 0 ≤ g2)
    (h3 : 0 ≤ g3) (h4 : 0 ≤ g4) (h5 : 0 ≤ g5) :
    (2714 / 10000000 : ℝ) * (g0 + g1 + g2 + g3 + g4 + g5) ≤
      pressure 0 * g0 + pressure 1 * g1 + pressure 2 * g2 +
      pressure 3 * g3 + pressure 4 * g4 + pressure 5 * g5 := by
  simp [pressure]
  nlinarith

/-- Hence a total six-gap span of at least `14.37` is already settled by the
linear pressure term alone.  The genuinely analytic problem is compact. -/
lemma v21_pressure_tail_six
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) (h2 : 0 ≤ g2)
    (h3 : 0 ≤ g3) (h4 : 0 ≤ g4) (h5 : 0 ≤ g5)
    (hspan : (1437 / 100 : ℝ) ≤ g0 + g1 + g2 + g3 + g4 + g5) :
    delta <
      pressure 0 * g0 + pressure 1 * g1 + pressure 2 * g2 +
      pressure 3 * g3 + pressure 4 * g4 + pressure 5 * g5 := by
  have hfloor := v21_pressure_floor_six g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5
  have hmargin := v21_pressure_cutoff_margin
  nlinarith

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
