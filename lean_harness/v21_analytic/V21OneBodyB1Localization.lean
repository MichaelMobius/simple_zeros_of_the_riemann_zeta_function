import HurtadoZeta23.V21OneBodyFloors
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

private def v21B1CutL : ℝ := 955 / 1000
private def v21B1CutR : ℝ := 1158 / 1000
private def v21B1RampCoeff : ℝ := (1 / 3 : ℝ) * (29 / 40 : ℝ) ^ 2

/-- On the left of the retained B1 basin the exact ramp lower bound is
monotone in the direction needed for the one-body argument. -/
lemma v21_oneBody_B1_left_cut {j : Fin 6} {p T x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ))
    (hxcut : x ≤ v21B1CutL)
    (hp0 : 0 ≤ p) (hp : p ≤ pressure j)
    (hfactor : p ≤ 2 * v21B1RampCoeff *
      (v21RootLeft 1 - v21B1CutL))
    (hboundary : T ≤
      p * v21B1CutL + v21B1RampCoeff *
        (v21RootLeft 1 - v21B1CutL) ^ 2) :
    T ≤ v21OneBody j x := by
  have hroot : x ≤ v21RootLeft 1 := by
    have hcutroot : v21B1CutL ≤ v21RootLeft 1 := by
      norm_num [v21B1CutL, v21RootLeft]
    exact hxcut.trans hcutroot
  have hw := v21_weight_ge_B1_ramp_sq hxlo hxhi
  change
    (29 / 40 : ℝ) ^ 2 * (v21RootRamp 1 x) ^ 2 ≤
      limitingWeight x at hw
  rw [v21_root_ramp_eq_left (n := 1) (by norm_num) (by norm_num) hroot] at hw
  have hx0 : 0 ≤ x := by nlinarith
  have hpx : p * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  have hgap : 0 ≤ v21B1CutL - x := sub_nonneg.mpr hxcut
  have hfac :
      0 ≤ v21B1RampCoeff *
          (2 * v21RootLeft 1 - x - v21B1CutL) - p := by
    have hmono :
        2 * (v21RootLeft 1 - v21B1CutL) ≤
          2 * v21RootLeft 1 - x - v21B1CutL := by
      linarith
    have hc0 : 0 ≤ v21B1RampCoeff := by
      norm_num [v21B1RampCoeff]
    have hm := mul_le_mul_of_nonneg_left hmono hc0
    nlinarith
  have hprod :
      0 ≤ (v21B1CutL - x) *
        (v21B1RampCoeff *
          (2 * v21RootLeft 1 - x - v21B1CutL) - p) :=
    mul_nonneg hgap hfac
  have hquad :
      p * v21B1CutL + v21B1RampCoeff *
          (v21RootLeft 1 - v21B1CutL) ^ 2 ≤
        p * x + v21B1RampCoeff * (v21RootLeft 1 - x) ^ 2 := by
    nlinarith
  unfold v21B1RampCoeff at hboundary hquad
  unfold v21OneBody
  nlinarith

/-- Symmetric right-side monotonicity for the exact first-band ramp. -/
lemma v21_oneBody_B1_right_cut {j : Fin 6} {p T x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ))
    (hxcut : v21B1CutR ≤ x)
    (hp0 : 0 ≤ p) (hp : p ≤ pressure j)
    (hboundary : T ≤
      p * v21B1CutR + v21B1RampCoeff *
        (v21B1CutR - v21RootRight 1) ^ 2) :
    T ≤ v21OneBody j x := by
  have hroot : v21RootRight 1 ≤ x := by
    have hrootcut : v21RootRight 1 ≤ v21B1CutR := by
      norm_num [v21B1CutR, v21RootRight]
    exact hrootcut.trans hxcut
  have hw := v21_weight_ge_B1_ramp_sq hxlo hxhi
  change
    (29 / 40 : ℝ) ^ 2 * (v21RootRamp 1 x) ^ 2 ≤
      limitingWeight x at hw
  rw [v21_root_ramp_eq_right (n := 1) (by norm_num) (by norm_num) hroot] at hw
  have hx0 : 0 ≤ x := by nlinarith
  have hpx : p * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  have hgap : 0 ≤ x - v21B1CutR := sub_nonneg.mpr hxcut
  have hright0 : 0 ≤ v21B1CutR - v21RootRight 1 := by
    norm_num [v21B1CutR, v21RootRight]
  have hc0 : 0 ≤ v21B1RampCoeff := by
    norm_num [v21B1RampCoeff]
  have hfac :
      0 ≤ p + v21B1RampCoeff *
        (x + v21B1CutR - 2 * v21RootRight 1) := by
    have : 0 ≤ x + v21B1CutR - 2 * v21RootRight 1 := by
      linarith
    positivity
  have hprod :
      0 ≤ (x - v21B1CutR) *
        (p + v21B1RampCoeff *
          (x + v21B1CutR - 2 * v21RootRight 1)) :=
    mul_nonneg hgap hfac
  have hquad :
      p * v21B1CutR + v21B1RampCoeff *
          (v21B1CutR - v21RootRight 1) ^ 2 ≤
        p * x + v21B1RampCoeff * (x - v21RootRight 1) ^ 2 := by
    nlinarith
  unfold v21B1RampCoeff at hboundary hquad
  unfold v21OneBody
  nlinarith

/-- Generic first-band localization once the two rational endpoint checks are
supplied. -/
lemma v21_oneBody_B1_localize {j : Fin 6} {p T x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ))
    (hp0 : 0 ≤ p) (hp : p ≤ pressure j)
    (hfactor : p ≤ 2 * v21B1RampCoeff *
      (v21RootLeft 1 - v21B1CutL))
    (hleft : T ≤ p * v21B1CutL + v21B1RampCoeff *
      (v21RootLeft 1 - v21B1CutL) ^ 2)
    (hright : T ≤ p * v21B1CutR + v21B1RampCoeff *
      (v21B1CutR - v21RootRight 1) ^ 2)
    (hsmall : v21OneBody j x < T) :
    v21B1CutL < x ∧ x < v21B1CutR := by
  constructor
  · by_contra h
    have hxcut : x ≤ v21B1CutL := le_of_not_gt h
    have hge := v21_oneBody_B1_left_cut hxlo hxhi hxcut
      hp0 hp hfactor hleft
    linarith
  · by_contra h
    have hxcut : v21B1CutR ≤ x := le_of_not_gt h
    have hge := v21_oneBody_B1_right_cut hxlo hxhi hxcut
      hp0 hp hright
    linarith

lemma v21_oneBody_B1_localize_A {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ))
    (hsmall : v21OneBody j x < (2081 / 1000000 : ℝ)) :
    (955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ) := by
  simpa [v21B1CutL, v21B1CutR] using
    (v21_oneBody_B1_localize
      (j := j) (p := (2714 / 10000000 : ℝ))
      (T := (2081 / 1000000 : ℝ)) hxlo hxhi
      (by norm_num) hp
      (by norm_num [v21B1RampCoeff, v21B1CutL, v21RootLeft])
      (by norm_num [v21B1RampCoeff, v21B1CutL, v21RootLeft])
      (by norm_num [v21B1RampCoeff, v21B1CutR, v21RootRight]) hsmall)

lemma v21_oneBody_B1_localize_B {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ))
    (hsmall : v21OneBody j x < (2189 / 1000000 : ℝ)) :
    (955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ) := by
  simpa [v21B1CutL, v21B1CutR] using
    (v21_oneBody_B1_localize
      (j := j) (p := (3733 / 10000000 : ℝ))
      (T := (2189 / 1000000 : ℝ)) hxlo hxhi
      (by norm_num) hp
      (by norm_num [v21B1RampCoeff, v21B1CutL, v21RootLeft])
      (by norm_num [v21B1RampCoeff, v21B1CutL, v21RootLeft])
      (by norm_num [v21B1RampCoeff, v21B1CutR, v21RootRight]) hsmall)

lemma v21_oneBody_B1_localize_C {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ))
    (hsmall : v21OneBody j x < (2170 / 1000000 : ℝ)) :
    (955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ) := by
  simpa [v21B1CutL, v21B1CutR] using
    (v21_oneBody_B1_localize
      (j := j) (p := (3553 / 10000000 : ℝ))
      (T := (2170 / 1000000 : ℝ)) hxlo hxhi
      (by norm_num) hp
      (by norm_num [v21B1RampCoeff, v21B1CutL, v21RootLeft])
      (by norm_num [v21B1RampCoeff, v21B1CutL, v21RootLeft])
      (by norm_num [v21B1RampCoeff, v21B1CutR, v21RootRight]) hsmall)

end HurtadoZeta23
