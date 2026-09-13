import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Published type-A one-body micro-floors. -/

theorem v26_micro_A1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (191 / 200 : ℝ) ≤ x) (hU : x ≤ (579 / 500 : ℝ)) :
    (143 / 500000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
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
      (143 / 500000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((13219307 / 25000000 : ℝ) * (x - v21RootRight 1) ^ 2 - (52877229 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (13219307 / 75000000 : ℝ))
      (q := v21RootRight 1) (eta := (17625743 / 1000000000000000 : ℝ))
      (c := (87289571281 / 82620668750 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_A2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (224 / 125 : ℝ) ≤ x) (hU : x ≤ (1129 / 500 : ℝ)) :
    (11 / 20000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 2) (L := (224 / 125 : ℝ)) (U := (1129 / 500 : ℝ))
    (x := x) (alpha := (14019769 / 125000000 : ℝ))
    (eta := (1401977 / 125000000000000 : ℝ))
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
      (11 / 20000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((14019769 / 125000000 : ℝ) * (x - v21RootRight 2) ^ 2 - (1401977 / 125000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (14019769 / 375000000 : ℝ))
      (q := v21RootRight 2) (eta := (1401977 / 375000000000000 : ℝ))
      (c := (2841022495383 / 1401976900000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_A3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (653 / 250 : ℝ) ≤ x) (hU : x ≤ (849 / 250 : ℝ)) :
    (817 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 3) (L := (653 / 250 : ℝ)) (U := (849 / 250 : ℝ))
    (x := x) (alpha := (8256029 / 250000000 : ℝ))
    (eta := (825603 / 250000000000000 : ℝ))
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
      (817 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((8256029 / 250000000 : ℝ) * (x - v21RootRight 3) ^ 2 - (825603 / 250000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (8256029 / 750000000 : ℝ))
      (q := v21RootRight 3) (eta := (275201 / 250000000000000 : ℝ))
      (c := (99333986349 / 33024116000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_A4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1751 / 500 : ℝ) ≤ x) (hU : x ≤ (893 / 200 : ℝ)) :
    (217 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 4) (L := (1751 / 500 : ℝ)) (U := (893 / 200 : ℝ))
    (x := x) (alpha := (1308653 / 100000000 : ℝ))
    (eta := (654327 / 500000000000000 : ℝ))
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
      (217 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((1308653 / 100000000 : ℝ) * (x - v21RootRight 4) ^ 2 - (654327 / 500000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (1308653 / 300000000 : ℝ))
      (q := v21RootRight 4) (eta := (218109 / 500000000000000 : ℝ))
      (c := (130346146793 / 32716325000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_A5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (9 / 2 : ℝ) ≤ x) (hU : x ≤ (2733 / 500 : ℝ)) :
    (1353 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 5) (L := (9 / 2 : ℝ)) (U := (2733 / 500 : ℝ))
    (x := x) (alpha := (21981 / 2500000 : ℝ))
    (eta := (879241 / 1000000000000000 : ℝ))
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
      (1353 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((21981 / 2500000 : ℝ) * (x - v21RootRight 5) ^ 2 - (879241 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (7327 / 2500000 : ℝ))
      (q := v21RootRight 5) (eta := (879241 / 3000000000000000 : ℝ))
      (c := (3638521267 / 732700000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_A6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (11 / 2 : ℝ) ≤ x) (hU : x ≤ (6413 / 1000 : ℝ)) :
    (811 / 500000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 6) (L := (11 / 2 : ℝ)) (U := (6413 / 1000 : ℝ))
    (x := x) (alpha := (1612259 / 250000000 : ℝ))
    (eta := (80613 / 125000000000000 : ℝ))
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
      (811 / 500000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((1612259 / 250000000 : ℝ) * (x - v21RootRight 6) ^ 2 - (80613 / 125000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (1612259 / 750000000 : ℝ))
      (q := v21RootRight 6) (eta := (26871 / 125000000000000 : ℝ))
      (c := (958820791921 / 161225900000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

theorem v26_micro_A7 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (822 / 125 : ℝ) ≤ x) (hU : x ≤ (727 / 100 : ℝ)) :
    (189 / 100000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := 7) (L := (822 / 125 : ℝ)) (U := (727 / 100 : ℝ))
    (x := x) (alpha := (6686277 / 1000000000 : ℝ))
    (eta := (167157 / 250000000000000 : ℝ))
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
      (189 / 100000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x +
        (1 / 3 : ℝ) * ((6686277 / 1000000000 : ℝ) * (x - v21RootRight 7) ^ 2 - (167157 / 250000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (1357 / 5000000 : ℝ)) (a := (2228759 / 1000000000 : ℝ))
      (q := v21RootRight 7) (eta := (55719 / 250000000000000 : ℝ))
      (c := (774254617683 / 111437950000 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

end HurtadoZeta23
