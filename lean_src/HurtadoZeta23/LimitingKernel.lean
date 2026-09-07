import Zeta23.ThmD.Functional
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real intervalIntegral
open scoped BigOperators

/--
The limiting Montgomery--Taylor overlap kernel in the normalization of the
position-weighted paper.  It is deliberately defined from Anthropic/Zeta23's
`ThmD.vStar 1`, so the finite refinement and Theorem D use the same optimal
profile.
-/
def limitingK (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
    Zeta23.ThmD.vStar 1 t * Real.cos (2 * Real.pi * x * t)

/-- At zero frequency the overlap kernel is exactly Zeta23's first moment `aStar 1`. -/
lemma limitingK_zero_eq_aStar : limitingK 0 = Zeta23.ThmD.aStar 1 := by
  simp [limitingK, Zeta23.ThmD.aStar]

/-- The closed normalization used in the manuscript: `K(0)=√2 sin(1/√2)`. -/
lemma limitingK_zero_closed :
    limitingK 0 = Real.sqrt 2 * Real.sin (Real.sqrt 2)⁻¹ := by
  rw [limitingK_zero_eq_aStar, Zeta23.ThmD.aStar_eq one_pos,
    Zeta23.ThmD.theta_one]
  ring

lemma limitingK_zero_pos : 0 < limitingK 0 := by
  rw [limitingK_zero_closed]
  have hs := Zeta23.ThmD.sin_theta_pos (lam := 1) one_pos le_rfl
  rw [Zeta23.ThmD.theta_one] at hs
  positivity

/-- The normalized compact overlap `k(x)=K(x)/K(0)`. -/
def limitingk (x : ℝ) : ℝ := limitingK x / limitingK 0

/-- The seven-point weight `w(x)=k(x)^2`. -/
def limitingWeight (x : ℝ) : ℝ := limitingk x ^ 2

lemma limitingk_zero : limitingk 0 = 1 := by
  unfold limitingk
  exact div_self (ne_of_gt limitingK_zero_pos)

lemma limitingWeight_zero : limitingWeight 0 = 1 := by
  simp [limitingWeight, limitingk_zero]

lemma limitingWeight_nonneg (x : ℝ) : 0 ≤ limitingWeight x := by
  exact sq_nonneg _

/-- Turn a normalized ordinate sequence into the pair-weight function consumed by `localFp`. -/
def limitingWeightOnPoints (y : ℕ → ℝ) (a b : ℕ) : ℝ :=
  limitingWeight (y b - y a)

lemma limitingWeightOnPoints_nonneg (y : ℕ → ℝ) (a b : ℕ) :
    0 ≤ limitingWeightOnPoints y a b :=
  limitingWeight_nonneg _

end HurtadoZeta23
