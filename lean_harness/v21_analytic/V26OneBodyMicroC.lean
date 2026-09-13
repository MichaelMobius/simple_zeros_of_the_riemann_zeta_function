import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Published type-C one-body micro-floors. -/

theorem v26_micro_C1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (191 / 200 : ℝ) ≤ x) (hU : x ≤ (579 / 500 : ℝ)) :
    (3 / 8000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 1) (L := (191 / 200 : ℝ)) (U := (579 / 500 : ℝ))
    (x := x) (alpha := (13219307 / 25000000 : ℝ))
    (eta := (52877229 / 1000000000000000 : ℝ))
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
      (3 / 8000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((13219307 / 25000000 : ℝ) * (x - v21RootRight 1) ^ 2 - (52877229 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3553 / 10000000 : ℝ)) (a := (13219307 / 75000000 : ℝ))
      (q := v21RootRight 1) (eta := (17625743 / 1000000000000000 : ℝ))
      (c := (9186306023 / 8696912500 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_C2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1797 / 1000 : ℝ) ≤ x) (hU : x ≤ (2251 / 1000 : ℝ)) :
    (9 / 12500 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 2) (L := (1797 / 1000 : ℝ)) (U := (2251 / 1000 : ℝ))
    (x := x) (alpha := (113823493 / 1000000000 : ℝ))
    (eta := (227647 / 20000000000000 : ℝ))
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
      (9 / 12500 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((113823493 / 1000000000 : ℝ) * (x - v21RootRight 2) ^ 2 - (227647 / 20000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3553 / 10000000 : ℝ)) (a := (113823493 / 3000000000 : ℝ))
      (q := v21RootRight 2) (eta := (227647 / 60000000000000 : ℝ))
      (c := (23053670843451 / 11382349300000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_C3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2633 / 1000 : ℝ) ≤ x) (hU : x ≤ (673 / 200 : ℝ)) :
    (1069 / 1000000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 3) (L := (2633 / 1000 : ℝ)) (U := (673 / 200 : ℝ))
    (x := x) (alpha := (8957721 / 250000000 : ℝ))
    (eta := (3583089 / 1000000000000000 : ℝ))
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
      (1069 / 1000000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((8957721 / 250000000 : ℝ) * (x - v21RootRight 3) ^ 2 - (3583089 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3553 / 10000000 : ℝ)) (a := (2985907 / 250000000 : ℝ))
      (q := v21RootRight 3) (eta := (1194363 / 1000000000000000 : ℝ))
      (c := (1889215393 / 628612000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_C4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (889 / 250 : ℝ) ≤ x) (hU : x ≤ (549 / 125 : ℝ)) :
    (1419 / 1000000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 4) (L := (889 / 250 : ℝ)) (U := (549 / 125 : ℝ))
    (x := x) (alpha := (3339079 / 200000000 : ℝ))
    (eta := (83477 / 50000000000000 : ℝ))
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
      (1419 / 1000000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((3339079 / 200000000 : ℝ) * (x - v21RootRight 4) ^ 2 - (83477 / 50000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3553 / 10000000 : ℝ)) (a := (3339079 / 600000000 : ℝ))
      (q := v21RootRight 4) (eta := (83477 / 150000000000000 : ℝ))
      (c := (17500807321 / 4393525000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_C5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (229 / 50 : ℝ) ≤ x) (hU : x ≤ (2661 / 500 : ℝ)) :
    (177 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 5) (L := (229 / 50 : ℝ)) (U := (2661 / 500 : ℝ))
    (x := x) (alpha := (3123147 / 250000000 : ℝ))
    (eta := (1249259 / 1000000000000000 : ℝ))
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
      (177 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((3123147 / 250000000 : ℝ) * (x - v21RootRight 5) ^ 2 - (1249259 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3553 / 10000000 : ℝ)) (a := (1041049 / 250000000 : ℝ))
      (q := v21RootRight 5) (eta := (1249259 / 3000000000000000 : ℝ))
      (c := (517354370829 / 104104900000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_C6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (5793 / 1000 : ℝ) ≤ x) (hU : x ≤ (3039 / 500 : ℝ)) :
    (1061 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 6) (L := (5793 / 1000 : ℝ)) (U := (3039 / 500 : ℝ))
    (x := x) (alpha := (7912261 / 500000000 : ℝ))
    (eta := (1582453 / 1000000000000000 : ℝ))
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
      (1061 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((7912261 / 500000000 : ℝ) * (x - v21RootRight 6) ^ 2 - (1582453 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3553 / 10000000 : ℝ)) (a := (7912261 / 1500000000 : ℝ))
      (q := v21RootRight 6) (eta := (1582453 / 3000000000000000 : ℝ))
      (c := (4728771693959 / 791226100000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

end HurtadoZeta23
