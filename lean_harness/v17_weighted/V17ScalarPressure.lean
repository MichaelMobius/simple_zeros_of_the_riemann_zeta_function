import HurtadoZeta23.V17StrongBlockScalar
import HurtadoZeta23.LimitingKernel
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact numerical frontier supplied by the v17 rational interval verifier.
The verifier proves a strict enclosure stronger than this statement. -/
def V17KernelAtG0Claim : Prop :=
  (2937 / 100000 : ℝ) < limitingWeight v17g0

/-- Analytic frontier used in the manuscript's scalar-pressure argument.
It records only the monotonicity actually needed: `w` is nonincreasing on
`[0,1]`.  Keeping this separate from the numerical enclosure makes the trust
boundary explicit and permits an internal calculus proof to replace it later. -/
def V17KernelAntitoneOnUnitClaim : Prop :=
  ∀ ⦃x y : ℝ⦄, 0 ≤ x → x ≤ y → y ≤ 1 →
    limitingWeight y ≤ limitingWeight x

/-- The exact rational target in the scalar verifier is `t * beta * g0`. -/
theorem v17_scalar_target_eq :
    v17t * beta * v17g0 = (2937 / 100000 : ℝ) := by
  norm_num [v17t, beta, v17g0]

/-- Scalar pressure inequality at the maximal pressure coefficient `beta`.
This is the only scalar form consumed by the weighted block argument. -/
theorem v17_scalar_pressure_of_frontiers
    (hnum : V17KernelAtG0Claim)
    (hmono : V17KernelAntitoneOnUnitClaim)
    {g : ℝ} (hg : 0 ≤ g) :
    v17t * beta * v17g0 ≤
      limitingWeight g + v17t * beta * g := by
  by_cases hle : g ≤ v17g0
  · have hg0le1 : v17g0 ≤ (1 : ℝ) := by
      norm_num [v17g0]
    have hwmono : limitingWeight v17g0 ≤ limitingWeight g :=
      hmono hg hle hg0le1
    have hstrict :
        v17t * beta * v17g0 < limitingWeight v17g0 := by
      rw [v17_scalar_target_eq]
      exact hnum
    have hlin : 0 ≤ v17t * beta * g := by
      have ht : 0 ≤ v17t := by norm_num [v17t]
      have hb : 0 ≤ beta := by norm_num [beta]
      positivity
    linarith
  · have hge : v17g0 ≤ g := le_of_lt (lt_of_not_ge hle)
    have hcoef : 0 ≤ v17t * beta := by
      norm_num [v17t, beta]
    have hlinear :
        v17t * beta * v17g0 ≤ v17t * beta * g := by
      exact mul_le_mul_of_nonneg_left hge hcoef
    have hw0 : 0 ≤ limitingWeight g := limitingWeight_nonneg g
    linarith

/-- Point-sequence form of the scalar pressure inequality. -/
theorem v17_scalar_pressure_on_points_of_frontiers
    (hnum : V17KernelAtG0Claim)
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
