import HurtadoZeta23.V17StrongBlockScalar
import HurtadoZeta23.LimitingKernel
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The exact point `0.89` at which the rational interval verifier certifies
the limiting-kernel lower bound.  This is intentionally kept distinct from
the slightly smaller safe scalar constant `v17g0 = 0.8898`. -/
def v17KernelCertPoint : ℝ := 89 / 100

/-- Exact numerical frontier supplied by the v17 rational interval verifier.
The verifier proves a strict enclosure stronger than this statement. -/
def V17KernelAtCertPointClaim : Prop :=
  (2937 / 100000 : ℝ) < limitingWeight v17KernelCertPoint

/-- Analytic frontier used in the manuscript's scalar-pressure argument.
It records only the monotonicity actually needed: `w` is nonincreasing on
`[0,1]`.  Keeping this separate from the numerical enclosure makes the trust
boundary explicit and permits an internal calculus proof to replace it later. -/
def V17KernelAntitoneOnUnitClaim : Prop :=
  ∀ ⦃x y : ℝ⦄, 0 ≤ x → x ≤ y → y ≤ 1 →
    limitingWeight y ≤ limitingWeight x

/-- At the certified point `0.89`, the linear pressure contribution is exactly
the rational lower bound certified for the limiting kernel. -/
theorem v17_cert_point_linear_eq :
    v17t * beta * v17KernelCertPoint = (2937 / 100000 : ℝ) := by
  norm_num [v17t, beta, v17KernelCertPoint]

/-- The safe scalar target used in the finite contradiction is strictly below
the certified `0.89` target. -/
theorem v17_scalar_target_lt_certified_target :
    v17t * beta * v17g0 < (2937 / 100000 : ℝ) := by
  norm_num [v17t, beta, v17g0]

/-- Scalar pressure inequality at the maximal pressure coefficient `beta`.
The split occurs at the certified point `0.89`: below it monotonicity transfers
the verified kernel value, while above it the linear pressure term alone
already dominates the slightly smaller finite-safe target. -/
theorem v17_scalar_pressure_of_frontiers
    (hnum : V17KernelAtCertPointClaim)
    (hmono : V17KernelAntitoneOnUnitClaim)
    {g : ℝ} (hg : 0 ≤ g) :
    v17t * beta * v17g0 ≤
      limitingWeight g + v17t * beta * g := by
  by_cases hle : g ≤ v17KernelCertPoint
  · have hcertle1 : v17KernelCertPoint ≤ (1 : ℝ) := by
      norm_num [v17KernelCertPoint]
    have hwmono :
        limitingWeight v17KernelCertPoint ≤ limitingWeight g :=
      hmono hg hle hcertle1
    have htarget :
        v17t * beta * v17g0 < limitingWeight v17KernelCertPoint :=
      lt_trans v17_scalar_target_lt_certified_target hnum
    have hlin : 0 ≤ v17t * beta * g := by
      have ht : 0 ≤ v17t := by norm_num [v17t]
      have hb : 0 ≤ beta := by norm_num [beta]
      positivity
    linarith
  · have hge : v17KernelCertPoint ≤ g := le_of_lt (lt_of_not_ge hle)
    have hcoef : 0 ≤ v17t * beta := by
      norm_num [v17t, beta]
    have hlinearCert :
        (2937 / 100000 : ℝ) ≤ v17t * beta * g := by
      rw [← v17_cert_point_linear_eq]
      exact mul_le_mul_of_nonneg_left hge hcoef
    have hw0 : 0 ≤ limitingWeight g := limitingWeight_nonneg g
    linarith [v17_scalar_target_lt_certified_target]

/-- Point-sequence form of the scalar pressure inequality. -/
theorem v17_scalar_pressure_on_points_of_frontiers
    (hnum : V17KernelAtCertPointClaim)
    (hmono : V17KernelAntitoneOnUnitClaim)
    (y : ℕ → ℝ)
    (hy : ∀ q < 449, y q ≤ y (q + 1)) :
    ∀ q < 449,
      v17t * beta * v17g0 ≤
        limitingWeightOnPoints y q (q + 1) +
          v17t * beta * (y (q + 1) - y q) := by
  intro q hq
  unfold limitingWeightOnPoints
  exact v17_scalar_pressure_of_frontiers
    hnum hmono (sub_nonneg.mpr (hy q hq))

end HurtadoZeta23
