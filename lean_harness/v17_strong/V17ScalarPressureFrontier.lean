import HurtadoZeta23.DirectRedistribution
import HurtadoZeta23.LimitingKernel
import HurtadoZeta23.V17StrongBlockScalar
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact mathematical statement needed from the new scalar-kernel check.

The accompanying v17 verifier establishes the numerical enclosure at
`g0 = 89/100`; together with the monotonicity argument in the manuscript this
is the only new scalar trust frontier introduced by v17.  Keeping it as a
named proposition prevents the finite strong-block proof from silently
assuming a separate inequality for every block. -/
def V17ScalarPressureClaim : Prop :=
  ∀ g : ℝ, 0 ≤ g →
    v17t * beta * v17g0 ≤
      limitingWeight g + v17t * beta * g

/-- SHA-256 of the exact-rational v17 verifier retained as provenance data. -/
def v17ScalarVerifierSHA256 : String :=
  "2beb9b2ce3d2925d546292d75cf3e627e6564884659dcb8808d92cb008e64671"

/-- SHA-256 of the verifier's retained `verification.json`. -/
def v17ScalarVerificationJSONSHA256 : String :=
  "60b5382aadfac1f74e622664e5fab9971ab6fe9cbb85d980a257eacd40cb0a36"

/-- A single universal scalar-pressure statement supplies the pointwise
adjacent-gap hypothesis required by `V17WeightedPressure` on any monotone
finite sequence. -/
theorem v17_scalar_pressure_on_monotone_points
    (hscalar : V17ScalarPressureClaim)
    {m : ℕ}
    (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1)) :
    ∀ q < m - 1,
      v17t * beta * v17g0 ≤
        limitingWeightOnPoints y q (q + 1) +
          v17t * beta * (y (q + 1) - y q) := by
  intro q hq
  have hg : 0 ≤ y (q + 1) - y q :=
    sub_nonneg.mpr (hmono q hq)
  simpa [limitingWeightOnPoints] using
    hscalar (y (q + 1) - y q) hg

/-- Length-450 specialization used by the concrete v17 block. -/
theorem v17_scalar_pressure_450_of_claim
    (hscalar : V17ScalarPressureClaim)
    (y : ℕ → ℝ)
    (hmono : ∀ q < 449, y q ≤ y (q + 1)) :
    ∀ q < 449,
      v17t * beta * v17g0 ≤
        limitingWeightOnPoints y q (q + 1) +
          v17t * beta * (y (q + 1) - y q) := by
  simpa using
    v17_scalar_pressure_on_monotone_points
      hscalar (m := 450) y hmono

end HurtadoZeta23