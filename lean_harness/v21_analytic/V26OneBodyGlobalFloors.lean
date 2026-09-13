import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Three global one-body floors on the strict hard core. -/

theorem v26_lambda_A_low {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (1425 / 1357 : ℝ)) :
    (57 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 1) (L := (89 / 100 : ℝ)) (U := (1425 / 1357 : ℝ))
    (alpha := (122133441 / 200000000 : ℝ))
    (eta := (61066721 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (57 / 200000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_lambda_A {x : ℝ} (hx89 : (89 / 100 : ℝ) < x) :
    (57 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hU : x ≤ (1425 / 1357 : ℝ)
  · exact v26_lambda_A_low hx89 (le_of_lt hx89) hU
  · have hw := v26_limitingWeight_nonneg x
    have hxU : (1425 / 1357 : ℝ) < x := lt_of_not_ge hU
    nlinarith

theorem v26_lambda_B_low {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (3930 / 3733 : ℝ)) :
    (393 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 1) (L := (89 / 100 : ℝ)) (U := (3930 / 3733 : ℝ))
    (alpha := (48583 / 80000 : ℝ))
    (eta := (60728751 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (393 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_lambda_B {x : ℝ} (hx89 : (89 / 100 : ℝ) < x) :
    (393 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hU : x ≤ (3930 / 3733 : ℝ)
  · exact v26_lambda_B_low hx89 (le_of_lt hx89) hU
  · have hw := v26_limitingWeight_nonneg x
    have hxU : (3930 / 3733 : ℝ) < x := lt_of_not_ge hU
    nlinarith

theorem v26_lambda_C_low {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (20 / 19 : ℝ)) :
    (187 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 1) (L := (89 / 100 : ℝ)) (U := (20 / 19 : ℝ))
    (alpha := (607465777 / 1000000000 : ℝ))
    (eta := (30373289 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (187 / 500000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_lambda_C {x : ℝ} (hx89 : (89 / 100 : ℝ) < x) :
    (187 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hU : x ≤ (20 / 19 : ℝ)
  · exact v26_lambda_C_low hx89 (le_of_lt hx89) hU
  · have hw := v26_limitingWeight_nonneg x
    have hxU : (20 / 19 : ℝ) < x := lt_of_not_ge hU
    nlinarith

end HurtadoZeta23
