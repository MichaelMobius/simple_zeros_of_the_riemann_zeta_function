import HurtadoZeta23.V21GapFunctional
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Weakest one-body contribution among the six historical pressure
coefficients.  It is coordinate-independent and therefore gives a uniform
filter for every gap. -/
def v21MinOneBody (x : ℝ) : ℝ :=
  (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x

/-- The minimum-pressure one-body functional is below every coordinate's
one-body contribution on nonnegative gaps. -/
lemma v21_minOneBody_le_coordinate (j : Fin 6) {x : ℝ} (hx : 0 ≤ x) :
    v21MinOneBody x ≤ pressure j * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hp := v21_pressure_min j
  have hmul := mul_le_mul_of_nonneg_right hp hx
  unfold v21MinOneBody
  linarith

/-- In the compact hard core every individual gap is strictly below `9.92`.
This is purely geometric: five other gaps are each larger than `0.89`, while
the total span is below `14.37`. -/
lemma v21_hard_core_individual_upper
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v17KernelCertPoint < g0)
    (h1 : v17KernelCertPoint < g1)
    (h2 : v17KernelCertPoint < g2)
    (h3 : v17KernelCertPoint < g3)
    (h4 : v17KernelCertPoint < g4)
    (h5 : v17KernelCertPoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ)) :
    g0 < (248 / 25 : ℝ) ∧
    g1 < (248 / 25 : ℝ) ∧
    g2 < (248 / 25 : ℝ) ∧
    g3 < (248 / 25 : ℝ) ∧
    g4 < (248 / 25 : ℝ) ∧
    g5 < (248 / 25 : ℝ) := by
  have h0' : (89 / 100 : ℝ) < g0 := by simpa [v17KernelCertPoint] using h0
  have h1' : (89 / 100 : ℝ) < g1 := by simpa [v17KernelCertPoint] using h1
  have h2' : (89 / 100 : ℝ) < g2 := by simpa [v17KernelCertPoint] using h2
  have h3' : (89 / 100 : ℝ) < g3 := by simpa [v17KernelCertPoint] using h3
  have h4' : (89 / 100 : ℝ) < g4 := by simpa [v17KernelCertPoint] using h4
  have h5' : (89 / 100 : ℝ) < g5 := by simpa [v17KernelCertPoint] using h5
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Three deliberately widened bands containing all one-body survivors of the
historical Arb certificate once the hard-core upper bound `x < 9.92` is used.
The remaining analytic task is to prove that a counterexample cannot lie in
one of the three complementary short intervals. -/
def v21GapBands (x : ℝ) : Prop :=
  ((19 / 20 : ℝ) ≤ x ∧ x ≤ (6 / 5 : ℝ)) ∨
  ((179 / 100 : ℝ) ≤ x ∧ x ≤ (237 / 100 : ℝ)) ∨
  ((261 / 100 : ℝ) ≤ x ∧ x < (248 / 25 : ℝ))

/-- Exact one-dimensional statement needed to justify the uniform band
reduction.  It is separated as a named frontier so its forthcoming analytic
proof can be audited independently. -/
def V21UniformGapFilterClaim : Prop :=
  ∀ x : ℝ,
    v17KernelCertPoint < x →
    x < (248 / 25 : ℝ) →
    v21MinOneBody x < delta →
      v21GapBands x

/-- Equivalently, it suffices to prove lower bounds on just the three gaps
between the survivor bands. -/
def V21UniformGapExclusionClaim : Prop :=
  (∀ x : ℝ, v17KernelCertPoint < x → x < (19 / 20 : ℝ) →
      delta ≤ v21MinOneBody x) ∧
  (∀ x : ℝ, (6 / 5 : ℝ) < x → x < (179 / 100 : ℝ) →
      delta ≤ v21MinOneBody x) ∧
  (∀ x : ℝ, (237 / 100 : ℝ) < x → x < (261 / 100 : ℝ) →
      delta ≤ v21MinOneBody x)

/-- The three interval exclusions imply the uniform survivor-band filter. -/
theorem v21_uniform_filter_of_exclusions
    (hexcl : V21UniformGapExclusionClaim) :
    V21UniformGapFilterClaim := by
  rcases hexcl with ⟨hfirst, hsecond, hthird⟩
  intro x hx hupper hsmall
  by_cases h95 : (19 / 20 : ℝ) ≤ x
  · by_cases h120 : x ≤ (6 / 5 : ℝ)
    · exact Or.inl ⟨h95, h120⟩
    · have h120' : (6 / 5 : ℝ) < x := lt_of_not_ge h120
      by_cases h179 : (179 / 100 : ℝ) ≤ x
      · by_cases h237 : x ≤ (237 / 100 : ℝ)
        · exact Or.inr (Or.inl ⟨h179, h237⟩)
        · have h237' : (237 / 100 : ℝ) < x := lt_of_not_ge h237
          by_cases h261 : (261 / 100 : ℝ) ≤ x
          · exact Or.inr (Or.inr ⟨h261, hupper⟩)
          · have h261' : x < (261 / 100 : ℝ) := lt_of_not_ge h261
            have := hthird x h237' h261'
            linarith
      · have h179' : x < (179 / 100 : ℝ) := lt_of_not_ge h179
        have := hsecond x h120' h179'
        linarith
  · have h95' : x < (19 / 20 : ℝ) := lt_of_not_ge h95
    have := hfirst x hx h95'
    linarith

end HurtadoZeta23
