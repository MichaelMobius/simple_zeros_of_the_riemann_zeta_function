import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Exact fixed exclusion certificate for type C. -/

theorem v26_excl_C01 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (191 / 200 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 1) (L := (89 / 100 : ℝ)) (U := (191 / 200 : ℝ))
    (alpha := (376726021 / 500000000 : ℝ)) (eta := (15069041 / 200000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C02 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (579 / 500 : ℝ) ≤ x) (hU : x ≤ (148863 / 128000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (579 / 500 : ℝ)) (U := (148863 / 128000 : ℝ))
    (alpha := (522989889 / 1000000000 : ℝ)) (eta := (52298989 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C03 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (148863 / 128000 : ℝ) ≤ x) (hU : x ≤ (74751 / 64000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (148863 / 128000 : ℝ)) (U := (74751 / 64000 : ℝ))
    (alpha := (516123057 / 1000000000 : ℝ)) (eta := (25806153 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C04 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (74751 / 64000 : ℝ) ≤ x) (hU : x ≤ (7539 / 6400 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (74751 / 64000 : ℝ)) (U := (7539 / 6400 : ℝ))
    (alpha := (25122197 / 50000000 : ℝ)) (eta := (10048879 / 200000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C05 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (7539 / 6400 : ℝ) ≤ x) (hU : x ≤ (19167 / 16000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (7539 / 6400 : ℝ)) (U := (19167 / 16000 : ℝ))
    (alpha := (475337819 / 1000000000 : ℝ)) (eta := (23766891 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C06 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (19167 / 16000 : ℝ) ≤ x) (hU : x ≤ (9903 / 8000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (19167 / 16000 : ℝ)) (U := (9903 / 8000 : ℝ))
    (alpha := (1689573 / 4000000 : ℝ)) (eta := (21119663 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C07 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (9903 / 8000 : ℝ) ≤ x) (hU : x ≤ (5271 / 4000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (9903 / 8000 : ℝ)) (U := (5271 / 4000 : ℝ))
    (alpha := (323425909 / 1000000000 : ℝ)) (eta := (32342591 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C08 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (5271 / 4000 : ℝ) ≤ x) (hU : x ≤ (591 / 400 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (5271 / 4000 : ℝ)) (U := (591 / 400 : ℝ))
    (alpha := (6552407 / 40000000 : ℝ)) (eta := (8190509 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C09 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (591 / 400 : ℝ) ≤ x) (hU : x ≤ (6549 / 4000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 2) (L := (591 / 400 : ℝ)) (U := (6549 / 4000 : ℝ))
    (alpha := (79373399 / 1000000000 : ℝ)) (eta := (396867 / 50000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C10 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (6549 / 4000 : ℝ) ≤ x) (hU : x ≤ (1797 / 1000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 2) (L := (6549 / 4000 : ℝ)) (U := (1797 / 1000 : ℝ))
    (alpha := (62201339 / 500000000 : ℝ)) (eta := (3110067 / 250000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C11 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2251 / 1000 : ℝ) ≤ x) (hU : x ≤ (4693 / 2000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 2) (L := (2251 / 1000 : ℝ)) (U := (4693 / 2000 : ℝ))
    (alpha := (8890997 / 100000000 : ℝ)) (eta := (4445499 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C12 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (4693 / 2000 : ℝ) ≤ x) (hU : x ≤ (1221 / 500 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 2) (L := (4693 / 2000 : ℝ)) (U := (1221 / 500 : ℝ))
    (alpha := (1579543 / 25000000 : ℝ)) (eta := (6318173 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C13 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1221 / 500 : ℝ) ≤ x) (hU : x ≤ (2633 / 1000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 3) (L := (1221 / 500 : ℝ)) (U := (2633 / 1000 : ℝ))
    (alpha := (6914707 / 250000000 : ℝ)) (eta := (2765883 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C14 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (673 / 200 : ℝ) ≤ x) (hU : x ≤ (6921 / 2000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 3) (L := (673 / 200 : ℝ)) (U := (6921 / 2000 : ℝ))
    (alpha := (574913 / 20000000 : ℝ)) (eta := (1437283 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C15 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (6921 / 2000 : ℝ) ≤ x) (hU : x ≤ (889 / 250 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 4) (L := (6921 / 2000 : ℝ)) (U := (889 / 250 : ℝ))
    (alpha := (2147049 / 125000000 : ℝ)) (eta := (42941 / 25000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C16 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (549 / 125 : ℝ) ≤ x) (hU : x ≤ (2243 / 500 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 5) (L := (549 / 125 : ℝ)) (U := (2243 / 500 : ℝ))
    (alpha := (7677499 / 1000000000 : ℝ)) (eta := (3071 / 4000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C17 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2243 / 500 : ℝ) ≤ x) (hU : x ≤ (229 / 50 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 5) (L := (2243 / 500 : ℝ)) (U := (229 / 50 : ℝ))
    (alpha := (1181381 / 100000000 : ℝ)) (eta := (590691 / 500000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C18 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2661 / 500 : ℝ) ≤ x) (hU : x ≤ (2223 / 400 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 6) (L := (2661 / 500 : ℝ)) (U := (2223 / 400 : ℝ))
    (alpha := (809341 / 250000000 : ℝ)) (eta := (323737 / 1000000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C19 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2223 / 400 : ℝ) ≤ x) (hU : x ≤ (5793 / 1000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 6) (L := (2223 / 400 : ℝ)) (U := (5793 / 1000 : ℝ))
    (alpha := (1968991 / 200000000 : ℝ)) (eta := (61531 / 62500000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C20 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (3039 / 500 : ℝ) ≤ x) (hU : x ≤ (21700 / 3553 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 7) (L := (3039 / 500 : ℝ)) (U := (21700 / 3553 : ℝ))
    (alpha := (95347 / 1000000000 : ℝ)) (eta := (1907 / 200000000000000 : ℝ))
    (p := (3553 / 10000000 : ℝ)) (target := (217 / 100000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_C_parent1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (191 / 200 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_C01 hx89 hL hU

theorem v26_excl_C_parent2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (579 / 500 : ℝ) ≤ x) (hU : x ≤ (1797 / 1000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut02 : x ≤ (148863 / 128000 : ℝ)
  · exact v26_excl_C02 hx89 hL hcut02
  · have hL02 : (148863 / 128000 : ℝ) ≤ x := by linarith
    by_cases hcut03 : x ≤ (74751 / 64000 : ℝ)
    · exact v26_excl_C03 hx89 hL02 hcut03
    · have hL03 : (74751 / 64000 : ℝ) ≤ x := by linarith
      by_cases hcut04 : x ≤ (7539 / 6400 : ℝ)
      · exact v26_excl_C04 hx89 hL03 hcut04
      · have hL04 : (7539 / 6400 : ℝ) ≤ x := by linarith
        by_cases hcut05 : x ≤ (19167 / 16000 : ℝ)
        · exact v26_excl_C05 hx89 hL04 hcut05
        · have hL05 : (19167 / 16000 : ℝ) ≤ x := by linarith
          by_cases hcut06 : x ≤ (9903 / 8000 : ℝ)
          · exact v26_excl_C06 hx89 hL05 hcut06
          · have hL06 : (9903 / 8000 : ℝ) ≤ x := by linarith
            by_cases hcut07 : x ≤ (5271 / 4000 : ℝ)
            · exact v26_excl_C07 hx89 hL06 hcut07
            · have hL07 : (5271 / 4000 : ℝ) ≤ x := by linarith
              by_cases hcut08 : x ≤ (591 / 400 : ℝ)
              · exact v26_excl_C08 hx89 hL07 hcut08
              · have hL08 : (591 / 400 : ℝ) ≤ x := by linarith
                by_cases hcut09 : x ≤ (6549 / 4000 : ℝ)
                · exact v26_excl_C09 hx89 hL08 hcut09
                · have hL09 : (6549 / 4000 : ℝ) ≤ x := by linarith
                  exact v26_excl_C10 hx89 hL09 hU

theorem v26_excl_C_parent3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2251 / 1000 : ℝ) ≤ x) (hU : x ≤ (2633 / 1000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut11 : x ≤ (4693 / 2000 : ℝ)
  · exact v26_excl_C11 hx89 hL hcut11
  · have hL11 : (4693 / 2000 : ℝ) ≤ x := by linarith
    by_cases hcut12 : x ≤ (1221 / 500 : ℝ)
    · exact v26_excl_C12 hx89 hL11 hcut12
    · have hL12 : (1221 / 500 : ℝ) ≤ x := by linarith
      exact v26_excl_C13 hx89 hL12 hU

theorem v26_excl_C_parent4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (673 / 200 : ℝ) ≤ x) (hU : x ≤ (889 / 250 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut14 : x ≤ (6921 / 2000 : ℝ)
  · exact v26_excl_C14 hx89 hL hcut14
  · have hL14 : (6921 / 2000 : ℝ) ≤ x := by linarith
    exact v26_excl_C15 hx89 hL14 hU

theorem v26_excl_C_parent5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (549 / 125 : ℝ) ≤ x) (hU : x ≤ (229 / 50 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut16 : x ≤ (2243 / 500 : ℝ)
  · exact v26_excl_C16 hx89 hL hcut16
  · have hL16 : (2243 / 500 : ℝ) ≤ x := by linarith
    exact v26_excl_C17 hx89 hL16 hU

theorem v26_excl_C_parent6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2661 / 500 : ℝ) ≤ x) (hU : x ≤ (5793 / 1000 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut18 : x ≤ (2223 / 400 : ℝ)
  · exact v26_excl_C18 hx89 hL hcut18
  · have hL18 : (2223 / 400 : ℝ) ≤ x := by linarith
    exact v26_excl_C19 hx89 hL18 hU

theorem v26_excl_C_parent7 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (3039 / 500 : ℝ) ≤ x) (hU : x ≤ (21700 / 3553 : ℝ)) :
    (217 / 100000 : ℝ) ≤ (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_C20 hx89 hL hU

end HurtadoZeta23
