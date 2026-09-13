import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Published type-B one-body micro-floors. -/

theorem v26_micro_B1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (191 / 200 : ℝ) ≤ x) (hU : x ≤ (579 / 500 : ℝ)) :
    (197 / 500000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
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
      (197 / 500000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((13219307 / 25000000 : ℝ) * (x - v21RootRight 1) ^ 2 - (52877229 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3733 / 10000000 : ℝ)) (a := (13219307 / 75000000 : ℝ))
      (q := v21RootRight 1) (eta := (17625743 / 1000000000000000 : ℝ))
      (c := (174531376937 / 165241337500 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_B2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (899 / 500 : ℝ) ≤ x) (hU : x ≤ (2249 / 1000 : ℝ)) :
    (189 / 250000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 2) (L := (899 / 500 : ℝ)) (U := (2249 / 1000 : ℝ))
    (x := x) (alpha := (28554817 / 250000000 : ℝ))
    (eta := (11421927 / 1000000000000000 : ℝ))
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
      (189 / 250000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((28554817 / 250000000 : ℝ) * (x - v21RootRight 2) ^ 2 - (11421927 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3733 / 10000000 : ℝ)) (a := (28554817 / 750000000 : ℝ))
      (q := v21RootRight 2) (eta := (3807309 / 1000000000000000 : ℝ))
      (c := (5782828984719 / 2855481700000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_B3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2637 / 1000 : ℝ) ≤ x) (hU : x ≤ (1679 / 500 : ℝ)) :
    (1123 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 3) (L := (2637 / 1000 : ℝ)) (U := (1679 / 500 : ℝ))
    (x := x) (alpha := (36399281 / 1000000000 : ℝ))
    (eta := (3639929 / 1000000000000000 : ℝ))
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
      (1123 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((36399281 / 1000000000 : ℝ) * (x - v21RootRight 3) ^ 2 - (3639929 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3733 / 10000000 : ℝ)) (a := (36399281 / 3000000000 : ℝ))
      (q := v21RootRight 3) (eta := (3639929 / 3000000000000000 : ℝ))
      (c := (437499913761 / 145597124000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_B4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (446 / 125 : ℝ) ≤ x) (hU : x ≤ (35 / 8 : ℝ)) :
    (149 / 100000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 4) (L := (446 / 125 : ℝ)) (U := (35 / 8 : ℝ))
    (x := x) (alpha := (17553291 / 1000000000 : ℝ))
    (eta := (175533 / 100000000000000 : ℝ))
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
      (149 / 100000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((17553291 / 1000000000 : ℝ) * (x - v21RootRight 4) ^ 2 - (175533 / 100000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3733 / 10000000 : ℝ)) (a := (5851097 / 1000000000 : ℝ))
      (q := v21RootRight 4) (eta := (58511 / 100000000000000 : ℝ))
      (c := (582672717957 / 146277425000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_B5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (4611 / 1000 : ℝ) ≤ x) (hU : x ≤ (1057 / 200 : ℝ)) :
    (1859 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 5) (L := (4611 / 1000 : ℝ)) (U := (1057 / 200 : ℝ))
    (x := x) (alpha := (1745381 / 125000000 : ℝ))
    (eta := (279261 / 200000000000000 : ℝ))
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
      (1859 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((1745381 / 125000000 : ℝ) * (x - v21RootRight 5) ^ 2 - (279261 / 200000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (3733 / 10000000 : ℝ)) (a := (1745381 / 375000000 : ℝ))
      (q := v21RootRight 5) (eta := (93087 / 200000000000000 : ℝ))
      (c := (867822235201 / 174538100000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

end HurtadoZeta23
