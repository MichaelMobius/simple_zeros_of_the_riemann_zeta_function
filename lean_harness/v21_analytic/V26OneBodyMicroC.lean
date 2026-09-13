import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Published type-C one-body micro-floors, through the compact Package-D certified-cell wrapper. -/

theorem v26_micro_C1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (191 / 200 : ℝ) ≤ x) (hU : x ≤ (579 / 500 : ℝ)) :
    (3 / 8000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 1) (L := (191 / 200 : ℝ)) (U := (579 / 500 : ℝ))
    (alpha := (13219307 / 25000000 : ℝ)) (eta := (52877229 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (3 / 8000 : ℝ))
    (c := (9186306023 / 8696912500 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_C2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1797 / 1000 : ℝ) ≤ x) (hU : x ≤ (2251 / 1000 : ℝ)) :
    (9 / 12500 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 2) (L := (1797 / 1000 : ℝ)) (U := (2251 / 1000 : ℝ))
    (alpha := (113823493 / 1000000000 : ℝ)) (eta := (227647 / 20000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (9 / 12500 : ℝ))
    (c := (23053670843451 / 11382349300000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_C3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2633 / 1000 : ℝ) ≤ x) (hU : x ≤ (673 / 200 : ℝ)) :
    (1069 / 1000000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 3) (L := (2633 / 1000 : ℝ)) (U := (673 / 200 : ℝ))
    (alpha := (8957721 / 250000000 : ℝ)) (eta := (3583089 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (1069 / 1000000 : ℝ))
    (c := (1889215393 / 628612000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_C4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (889 / 250 : ℝ) ≤ x) (hU : x ≤ (549 / 125 : ℝ)) :
    (1419 / 1000000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 4) (L := (889 / 250 : ℝ)) (U := (549 / 125 : ℝ))
    (alpha := (3339079 / 200000000 : ℝ)) (eta := (83477 / 50000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (1419 / 1000000 : ℝ))
    (c := (17500807321 / 4393525000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_C5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (229 / 50 : ℝ) ≤ x) (hU : x ≤ (2661 / 500 : ℝ)) :
    (177 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 5) (L := (229 / 50 : ℝ)) (U := (2661 / 500 : ℝ))
    (alpha := (3123147 / 250000000 : ℝ)) (eta := (1249259 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (177 / 100000 : ℝ))
    (c := (517354370829 / 104104900000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_C6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (5793 / 1000 : ℝ) ≤ x) (hU : x ≤ (3039 / 500 : ℝ)) :
    (1061 / 500000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 6) (L := (5793 / 1000 : ℝ)) (U := (3039 / 500 : ℝ))
    (alpha := (7912261 / 500000000 : ℝ)) (eta := (1582453 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (1061 / 500000 : ℝ))
    (c := (4728771693959 / 791226100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

end HurtadoZeta23
