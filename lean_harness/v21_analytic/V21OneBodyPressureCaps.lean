import HurtadoZeta23.V21OneBodyFloors
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Pressure alone bounds a coordinate once its one-body contribution is
strictly below a threshold. -/
lemma v21_oneBody_pressure_cap {j : Fin 6} {p T U x : ℝ}
    (hx0 : 0 ≤ x) (hp0 : 0 < p) (hp : p ≤ pressure j)
    (hTU : T = p * U)
    (hsmall : v21OneBody j x < T) :
    x < U := by
  have hw := limitingWeight_nonneg x
  have hpx : p * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  have hpress : p * x ≤ v21OneBody j x := by
    unfold v21OneBody
    nlinarith
  have : p * x < p * U := by
    rw [← hTU]
    exact hpress.trans_lt hsmall
  exact (mul_lt_mul_left hp0).mp this

lemma v21_oneBody_pressure_cap_A {j : Fin 6} {x : ℝ}
    (hx0 : 0 ≤ x)
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hsmall : v21OneBody j x < (2081 / 1000000 : ℝ)) :
    x < (10405 / 1357 : ℝ) := by
  apply v21_oneBody_pressure_cap
    (p := (2714 / 10000000 : ℝ))
    (T := (2081 / 1000000 : ℝ))
    (U := (10405 / 1357 : ℝ)) hx0 (by norm_num) hp
  · norm_num
  · exact hsmall

lemma v21_oneBody_pressure_cap_B {j : Fin 6} {x : ℝ}
    (hx0 : 0 ≤ x)
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hsmall : v21OneBody j x < (2189 / 1000000 : ℝ)) :
    x < (21890 / 3733 : ℝ) := by
  apply v21_oneBody_pressure_cap
    (p := (3733 / 10000000 : ℝ))
    (T := (2189 / 1000000 : ℝ))
    (U := (21890 / 3733 : ℝ)) hx0 (by norm_num) hp
  · norm_num
  · exact hsmall

lemma v21_oneBody_pressure_cap_C {j : Fin 6} {x : ℝ}
    (hx0 : 0 ≤ x)
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hsmall : v21OneBody j x < (2170 / 1000000 : ℝ)) :
    x < (21700 / 3553 : ℝ) := by
  apply v21_oneBody_pressure_cap
    (p := (3553 / 10000000 : ℝ))
    (T := (2170 / 1000000 : ℝ))
    (U := (21700 / 3553 : ℝ)) hx0 (by norm_num) hp
  · norm_num
  · exact hsmall

end HurtadoZeta23
