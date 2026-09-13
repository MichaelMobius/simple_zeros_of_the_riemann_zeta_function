import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Three global one-body floors on the strict hard core. -/

theorem v26_lambda_A_low {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (1425 / 1357 : ℝ)) :
    (57 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 1) (L := (89 / 100 : ℝ)) (U := (1425 / 1357 : ℝ))
    (x := x) (alpha := (122133441 / 200000000 : ℝ))
    (eta := (61066721 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight, v26Araw, v26AmplitudeFloor,
      v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight, v26Araw, v26AmplitudeFloor,
      v26ChordCoeff, v26Fold, v26P7, v26d0])
  have hquad :
      (57 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((122133441 / 200000000 : ℝ) * (x - v21RootRight 1) ^ 2 - (61066721 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_right
      (p := (1357 / 5000000 : ℝ)) (a := (40711147 / 200000000 : ℝ))
      (q := v21RootRight 1) (eta := (61066721 / 3000000000000000 : ℝ))
      (U := (1425 / 1357 : ℝ))
    · norm_num
    · exact hU
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

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
  have hminor := v26_certified_cell_minorant
    (N := 1) (L := (89 / 100 : ℝ)) (U := (3930 / 3733 : ℝ))
    (x := x) (alpha := (48583 / 80000 : ℝ))
    (eta := (60728751 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight, v26Araw, v26AmplitudeFloor,
      v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight, v26Araw, v26AmplitudeFloor,
      v26ChordCoeff, v26Fold, v26P7, v26d0])
  have hquad :
      (393 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((48583 / 80000 : ℝ) * (x - v21RootRight 1) ^ 2 - (60728751 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_right
      (p := (3733 / 10000000 : ℝ)) (a := (48583 / 240000 : ℝ))
      (q := v21RootRight 1) (eta := (20242917 / 1000000000000000 : ℝ))
      (U := (3930 / 3733 : ℝ))
    · norm_num
    · exact hU
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

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
  have hminor := v26_certified_cell_minorant
    (N := 1) (L := (89 / 100 : ℝ)) (U := (20 / 19 : ℝ))
    (x := x) (alpha := (607465777 / 1000000000 : ℝ))
    (eta := (30373289 / 500000000000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight, v26Araw, v26AmplitudeFloor,
      v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps,
      v26Mrat, v21RootRight, v26Araw, v26AmplitudeFloor,
      v26ChordCoeff, v26Fold, v26P7, v26d0])
  have hquad :
      (187 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((607465777 / 1000000000 : ℝ) * (x - v21RootRight 1) ^ 2 - (30373289 / 500000000000000 : ℝ)) := by
    apply v26_quad_lower_right
      (p := (3553 / 10000000 : ℝ)) (a := (607465777 / 3000000000 : ℝ))
      (q := v21RootRight 1) (eta := (30373289 / 1500000000000000 : ℝ))
      (U := (20 / 19 : ℝ))
    · norm_num
    · exact hU
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_lambda_C {x : ℝ} (hx89 : (89 / 100 : ℝ) < x) :
    (187 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hU : x ≤ (20 / 19 : ℝ)
  · exact v26_lambda_C_low hx89 (le_of_lt hx89) hU
  · have hw := v26_limitingWeight_nonneg x
    have hxU : (20 / 19 : ℝ) < x := lt_of_not_ge hU
    nlinarith

end HurtadoZeta23
