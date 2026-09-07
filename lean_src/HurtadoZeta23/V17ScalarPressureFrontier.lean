import HurtadoZeta23.DirectRedistribution
import HurtadoZeta23.LimitingKernel
import HurtadoZeta23.V17StrongBlockScalar
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact mathematical statement needed from the new scalar-kernel check.

The accompanying v17 verifier establishes the numerical enclosure at
`g0 = 89/100`.  In the final v17 theorem this universal statement is no
longer an external trust input: `V17KernelMonotonicity` derives it inside
Lean from the single signed kernel certificate.  It remains named here as
the interface consumed by the finite strong-block proof. -/
def V17ScalarPressureClaim : Prop :=
  ∀ g : ℝ, 0 ≤ g →
    v17t * beta * v17g0 ≤
      limitingWeight g + v17t * beta * g

/-- SHA-256 of the current exact-rational v17 verifier retained as provenance data. -/
def v17ScalarVerifierSHA256 : String :=
  "73ba433447a15659a78f1485fd0403fe0fa767371ff6b22f3e6c1a1929c54208"

/-- SHA-256 of the current frozen `certification/v17/verification.json`. -/
def v17ScalarVerificationJSONSHA256 : String :=
  "c3ceab7fb966ecd9bc954da5e29414a84ef8d8a699f290a9378335a9b3542446"

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