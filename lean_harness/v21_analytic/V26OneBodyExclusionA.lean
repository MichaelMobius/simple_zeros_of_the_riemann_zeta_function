import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Exact fixed exclusion certificate for type A. -/

theorem v26_excl_A01 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (191 / 200 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 1) (L := (89 / 100 : ℝ)) (U := (191 / 200 : ℝ))
    (alpha := (376726021 / 500000000 : ℝ)) (eta := (15069041 / 200000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A02 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (579 / 500 : ℝ) ≤ x) (hU : x ≤ (74429 / 64000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (579 / 500 : ℝ)) (U := (74429 / 64000 : ℝ))
    (alpha := (523043687 / 1000000000 : ℝ)) (eta := (52304369 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A03 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (74429 / 64000 : ℝ) ≤ x) (hU : x ≤ (37373 / 32000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (74429 / 64000 : ℝ)) (U := (37373 / 32000 : ℝ))
    (alpha := (103246077 / 200000000 : ℝ)) (eta := (51623039 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A04 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (37373 / 32000 : ℝ) ≤ x) (hU : x ≤ (3769 / 3200 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (37373 / 32000 : ℝ)) (U := (3769 / 3200 : ℝ))
    (alpha := (502657413 / 1000000000 : ℝ)) (eta := (25132871 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A05 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (3769 / 3200 : ℝ) ≤ x) (hU : x ≤ (9581 / 8000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (3769 / 3200 : ℝ)) (U := (9581 / 8000 : ℝ))
    (alpha := (475759137 / 1000000000 : ℝ)) (eta := (23787957 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A06 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (9581 / 8000 : ℝ) ≤ x) (hU : x ≤ (4949 / 4000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (9581 / 8000 : ℝ)) (U := (4949 / 4000 : ℝ))
    (alpha := (52900829 / 125000000 : ℝ)) (eta := (5290083 / 125000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A07 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (4949 / 4000 : ℝ) ≤ x) (hU : x ≤ (2633 / 2000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (4949 / 4000 : ℝ)) (U := (2633 / 2000 : ℝ))
    (alpha := (40611183 / 125000000 : ℝ)) (eta := (32488947 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A08 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2633 / 2000 : ℝ) ≤ x) (hU : x ≤ (59 / 40 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (2633 / 2000 : ℝ)) (U := (59 / 40 : ℝ))
    (alpha := (82929057 / 500000000 : ℝ)) (eta := (4146453 / 250000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A09 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (59 / 40 : ℝ) ≤ x) (hU : x ≤ (3267 / 2000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 2) (L := (59 / 40 : ℝ)) (U := (3267 / 2000 : ℝ))
    (alpha := (78732213 / 1000000000 : ℝ)) (eta := (3936611 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A10 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (3267 / 2000 : ℝ) ≤ x) (hU : x ≤ (224 / 125 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 2) (L := (3267 / 2000 : ℝ)) (U := (224 / 125 : ℝ))
    (alpha := (12367713 / 100000000 : ℝ)) (eta := (6183857 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A11 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1129 / 500 : ℝ) ≤ x) (hU : x ≤ (4693 / 2000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 2) (L := (1129 / 500 : ℝ)) (U := (4693 / 2000 : ℝ))
    (alpha := (8890997 / 100000000 : ℝ)) (eta := (4445499 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A12 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (4693 / 2000 : ℝ) ≤ x) (hU : x ≤ (487 / 200 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 2) (L := (4693 / 2000 : ℝ)) (U := (487 / 200 : ℝ))
    (alpha := (8120499 / 125000000 : ℝ)) (eta := (16241 / 2500000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A13 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (487 / 200 : ℝ) ≤ x) (hU : x ≤ (653 / 250 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 3) (L := (487 / 200 : ℝ)) (U := (653 / 250 : ℝ))
    (alpha := (2709537 / 100000000 : ℝ)) (eta := (1354769 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A14 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (849 / 250 : ℝ) ≤ x) (hU : x ≤ (3449 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 3) (L := (849 / 250 : ℝ)) (U := (3449 / 1000 : ℝ))
    (alpha := (30073001 / 1000000000 : ℝ)) (eta := (3007301 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A15 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (3449 / 1000 : ℝ) ≤ x) (hU : x ≤ (1751 / 500 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 4) (L := (3449 / 1000 : ℝ)) (U := (1751 / 500 : ℝ))
    (alpha := (16753027 / 1000000000 : ℝ)) (eta := (1675303 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A16 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (893 / 200 : ℝ) ≤ x) (hU : x ≤ (9 / 2 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 5) (L := (893 / 200 : ℝ)) (U := (9 / 2 : ℝ))
    (alpha := (445487 / 40000000 : ℝ)) (eta := (556859 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A17 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2733 / 500 : ℝ) ≤ x) (hU : x ≤ (11 / 2 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 6) (L := (2733 / 500 : ℝ)) (U := (11 / 2 : ℝ))
    (alpha := (756681 / 100000000 : ℝ)) (eta := (378341 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A18 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (6413 / 1000 : ℝ) ≤ x) (hU : x ≤ (12989 / 2000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 7) (L := (6413 / 1000 : ℝ)) (U := (12989 / 2000 : ℝ))
    (alpha := (4208587 / 1000000000 : ℝ)) (eta := (420859 / 1000000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A19 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (12989 / 2000 : ℝ) ≤ x) (hU : x ≤ (822 / 125 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 7) (L := (12989 / 2000 : ℝ)) (U := (822 / 125 : ℝ))
    (alpha := (6037373 / 1000000000 : ℝ)) (eta := (301869 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A20 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (727 / 100 : ℝ) ≤ x) (hU : x ≤ (10405 / 1357 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 8) (L := (727 / 100 : ℝ)) (U := (10405 / 1357 : ℝ))
    (alpha := (1158857 / 1000000000 : ℝ)) (eta := (57943 / 500000000000000 : ℝ))
    (p := (1357 / 5000000 : ℝ)) (target := (2081 / 1000000 : ℝ)) (c := (177452425121 / 23177140000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_A_parent1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (191 / 200 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_A01 hx89 hL hU

theorem v26_excl_A_parent2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (579 / 500 : ℝ) ≤ x) (hU : x ≤ (224 / 125 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut02 : x ≤ (74429 / 64000 : ℝ)
  · exact v26_excl_A02 hx89 hL hcut02
  · have hL02 : (74429 / 64000 : ℝ) ≤ x := by linarith
    by_cases hcut03 : x ≤ (37373 / 32000 : ℝ)
    · exact v26_excl_A03 hx89 hL02 hcut03
    · have hL03 : (37373 / 32000 : ℝ) ≤ x := by linarith
      by_cases hcut04 : x ≤ (3769 / 3200 : ℝ)
      · exact v26_excl_A04 hx89 hL03 hcut04
      · have hL04 : (3769 / 3200 : ℝ) ≤ x := by linarith
        by_cases hcut05 : x ≤ (9581 / 8000 : ℝ)
        · exact v26_excl_A05 hx89 hL04 hcut05
        · have hL05 : (9581 / 8000 : ℝ) ≤ x := by linarith
          by_cases hcut06 : x ≤ (4949 / 4000 : ℝ)
          · exact v26_excl_A06 hx89 hL05 hcut06
          · have hL06 : (4949 / 4000 : ℝ) ≤ x := by linarith
            by_cases hcut07 : x ≤ (2633 / 2000 : ℝ)
            · exact v26_excl_A07 hx89 hL06 hcut07
            · have hL07 : (2633 / 2000 : ℝ) ≤ x := by linarith
              by_cases hcut08 : x ≤ (59 / 40 : ℝ)
              · exact v26_excl_A08 hx89 hL07 hcut08
              · have hL08 : (59 / 40 : ℝ) ≤ x := by linarith
                by_cases hcut09 : x ≤ (3267 / 2000 : ℝ)
                · exact v26_excl_A09 hx89 hL08 hcut09
                · have hL09 : (3267 / 2000 : ℝ) ≤ x := by linarith
                  exact v26_excl_A10 hx89 hL09 hU

theorem v26_excl_A_parent3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1129 / 500 : ℝ) ≤ x) (hU : x ≤ (653 / 250 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut11 : x ≤ (4693 / 2000 : ℝ)
  · exact v26_excl_A11 hx89 hL hcut11
  · have hL11 : (4693 / 2000 : ℝ) ≤ x := by linarith
    by_cases hcut12 : x ≤ (487 / 200 : ℝ)
    · exact v26_excl_A12 hx89 hL11 hcut12
    · have hL12 : (487 / 200 : ℝ) ≤ x := by linarith
      exact v26_excl_A13 hx89 hL12 hU

theorem v26_excl_A_parent4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (849 / 250 : ℝ) ≤ x) (hU : x ≤ (1751 / 500 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut14 : x ≤ (3449 / 1000 : ℝ)
  · exact v26_excl_A14 hx89 hL hcut14
  · have hL14 : (3449 / 1000 : ℝ) ≤ x := by linarith
    exact v26_excl_A15 hx89 hL14 hU

theorem v26_excl_A_parent5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (893 / 200 : ℝ) ≤ x) (hU : x ≤ (9 / 2 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_A16 hx89 hL hU

theorem v26_excl_A_parent6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2733 / 500 : ℝ) ≤ x) (hU : x ≤ (11 / 2 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_A17 hx89 hL hU

theorem v26_excl_A_parent7 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (6413 / 1000 : ℝ) ≤ x) (hU : x ≤ (822 / 125 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut18 : x ≤ (12989 / 2000 : ℝ)
  · exact v26_excl_A18 hx89 hL hcut18
  · have hL18 : (12989 / 2000 : ℝ) ≤ x := by linarith
    exact v26_excl_A19 hx89 hL18 hU

theorem v26_excl_A_parent8 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (727 / 100 : ℝ) ≤ x) (hU : x ≤ (10405 / 1357 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_A20 hx89 hL hU

end HurtadoZeta23
