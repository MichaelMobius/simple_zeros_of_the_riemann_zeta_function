import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Published type-B one-body micro-floors, through the compact Package-D certified-cell wrapper. -/

theorem v26_micro_B1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (191 / 200 : ℝ) ≤ x) (hU : x ≤ (579 / 500 : ℝ)) :
    (197 / 500000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 1) (L := (191 / 200 : ℝ)) (U := (579 / 500 : ℝ))
    (alpha := (13219307 / 25000000 : ℝ)) (eta := (52877229 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (197 / 500000 : ℝ))
    (c := (174531376937 / 165241337500 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_B2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (899 / 500 : ℝ) ≤ x) (hU : x ≤ (2249 / 1000 : ℝ)) :
    (189 / 250000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 2) (L := (899 / 500 : ℝ)) (U := (2249 / 1000 : ℝ))
    (alpha := (28554817 / 250000000 : ℝ)) (eta := (11421927 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (189 / 250000 : ℝ))
    (c := (5782828984719 / 2855481700000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_B3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2637 / 1000 : ℝ) ≤ x) (hU : x ≤ (1679 / 500 : ℝ)) :
    (1123 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 3) (L := (2637 / 1000 : ℝ)) (U := (1679 / 500 : ℝ))
    (alpha := (36399281 / 1000000000 : ℝ)) (eta := (3639929 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (1123 / 1000000 : ℝ))
    (c := (437499913761 / 145597124000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_B4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (446 / 125 : ℝ) ≤ x) (hU : x ≤ (35 / 8 : ℝ)) :
    (149 / 100000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 4) (L := (446 / 125 : ℝ)) (U := (35 / 8 : ℝ))
    (alpha := (17553291 / 1000000000 : ℝ)) (eta := (175533 / 100000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (149 / 100000 : ℝ))
    (c := (582672717957 / 146277425000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_micro_B5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (4611 / 1000 : ℝ) ≤ x) (hU : x ≤ (1057 / 200 : ℝ)) :
    (1859 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 5) (L := (4611 / 1000 : ℝ)) (U := (1057 / 200 : ℝ))
    (alpha := (1745381 / 125000000 : ℝ)) (eta := (279261 / 200000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (1859 / 1000000 : ℝ))
    (c := (867822235201 / 174538100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

end HurtadoZeta23
