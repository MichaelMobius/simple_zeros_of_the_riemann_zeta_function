import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Published type-A one-body micro-floors, through the compact Package-D certified-cell wrapper. -/

theorem v26_micro_A1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (191 / 200 : ℝ) ≤ x) (hU : x ≤ (579 / 500 : ℝ)) :
    (143 / 500000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 1) (L := (191 / 200 : ℝ)) (U := (579 / 500 : ℝ))
    (alpha := (13219307 / 25000000 : ℝ)) (eta := (52877229 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (143 / 500000 : ℝ))
    (c := (87289571281 / 82620668750 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_A2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (224 / 125 : ℝ) ≤ x) (hU : x ≤ (1129 / 500 : ℝ)) :
    (11 / 20000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 2) (L := (224 / 125 : ℝ)) (U := (1129 / 500 : ℝ))
    (alpha := (14019769 / 125000000 : ℝ)) (eta := (1401977 / 125000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (11 / 20000 : ℝ))
    (c := (2841022495383 / 1401976900000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_A3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (653 / 250 : ℝ) ≤ x) (hU : x ≤ (849 / 250 : ℝ)) :
    (817 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 3) (L := (653 / 250 : ℝ)) (U := (849 / 250 : ℝ))
    (alpha := (8256029 / 250000000 : ℝ)) (eta := (825603 / 250000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (817 / 1000000 : ℝ))
    (c := (99333986349 / 33024116000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_A4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1751 / 500 : ℝ) ≤ x) (hU : x ≤ (893 / 200 : ℝ)) :
    (217 / 200000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 4) (L := (1751 / 500 : ℝ)) (U := (893 / 200 : ℝ))
    (alpha := (1308653 / 100000000 : ℝ)) (eta := (654327 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (217 / 200000 : ℝ))
    (c := (130346146793 / 32716325000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_A5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (9 / 2 : ℝ) ≤ x) (hU : x ≤ (2733 / 500 : ℝ)) :
    (1353 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 5) (L := (9 / 2 : ℝ)) (U := (2733 / 500 : ℝ))
    (alpha := (21981 / 2500000 : ℝ)) (eta := (879241 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (1353 / 1000000 : ℝ))
    (c := (3638521267 / 732700000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_A6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (11 / 2 : ℝ) ≤ x) (hU : x ≤ (6413 / 1000 : ℝ)) :
    (811 / 500000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 6) (L := (11 / 2 : ℝ)) (U := (6413 / 1000 : ℝ))
    (alpha := (1612259 / 250000000 : ℝ)) (eta := (80613 / 125000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (811 / 500000 : ℝ))
    (c := (958820791921 / 161225900000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_A7 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (822 / 125 : ℝ) ≤ x) (hU : x ≤ (727 / 100 : ℝ)) :
    (189 / 100000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 7) (L := (822 / 125 : ℝ)) (U := (727 / 100 : ℝ))
    (alpha := (6686277 / 1000000000 : ℝ)) (eta := (167157 / 250000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (189 / 100000 : ℝ))
    (c := (774254617683 / 111437950000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

end HurtadoZeta23
