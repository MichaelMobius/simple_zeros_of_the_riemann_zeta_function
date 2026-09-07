import HurtadoZeta23.Constants
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The nonuniform pressure vector from the paper. -/
def pressure : Fin 6 → ℝ := ![
  2714 / 10000000,
  3733 / 10000000,
  3553 / 10000000,
  3553 / 10000000,
  3733 / 10000000,
  2714 / 10000000
]

lemma pressure_nonneg (j : Fin 6) : 0 ≤ pressure j := by
  fin_cases j <;> norm_num [pressure]

/-- The global double-counting cost sees only the total pressure. -/
lemma pressure_sum : ∑ j : Fin 6, pressure j = beta := by
  norm_num [pressure, beta, Fin.sum_univ_succ]

/-- Exact rational form of the local certificate target. -/
lemma delta_pos : 0 < delta := by
  norm_num [delta]

end HurtadoZeta23
