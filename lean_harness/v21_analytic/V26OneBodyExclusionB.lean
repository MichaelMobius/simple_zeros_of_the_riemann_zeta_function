import HurtadoZeta23.V26OneBodyCertTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Exact fixed exclusion certificate for type B. -/

theorem v26_excl_B01 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (191 / 200 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 1) (L := (89 / 100 : ℝ)) (U := (191 / 200 : ℝ))
    (alpha := (376726021 / 500000000 : ℝ)) (eta := (15069041 / 200000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B02 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (579 / 500 : ℝ) ≤ x) (hU : x ≤ (1163 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (579 / 500 : ℝ)) (U := (1163 / 1000 : ℝ))
    (alpha := (522979129 / 1000000000 : ℝ)) (eta := (52297913 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B03 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1163 / 1000 : ℝ) ≤ x) (hU : x ≤ (146 / 125 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (1163 / 1000 : ℝ)) (U := (146 / 125 : ℝ))
    (alpha := (516101591 / 1000000000 : ℝ)) (eta := (645127 / 12500000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B04 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (146 / 125 : ℝ) ≤ x) (hU : x ≤ (589 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (146 / 125 : ℝ)) (U := (589 / 500 : ℝ))
    (alpha := (15700039 / 31250000 : ℝ)) (eta := (401921 / 8000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B05 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (589 / 500 : ℝ) ≤ x) (hU : x ≤ (599 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (589 / 500 : ℝ)) (U := (599 / 500 : ℝ))
    (alpha := (7425837 / 15625000 : ℝ)) (eta := (47525357 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B06 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (599 / 500 : ℝ) ≤ x) (hU : x ≤ (619 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (599 / 500 : ℝ)) (U := (619 / 500 : ℝ))
    (alpha := (422230637 / 1000000000 : ℝ)) (eta := (5277883 / 125000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B07 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (619 / 500 : ℝ) ≤ x) (hU : x ≤ (659 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (619 / 500 : ℝ)) (U := (659 / 500 : ℝ))
    (alpha := (64626711 / 200000000 : ℝ)) (eta := (8078339 / 250000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B08 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (659 / 500 : ℝ) ≤ x) (hU : x ≤ (739 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 1) (L := (659 / 500 : ℝ)) (U := (739 / 500 : ℝ))
    (alpha := (1276581 / 7812500 : ℝ)) (eta := (16340237 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B09 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (739 / 500 : ℝ) ≤ x) (hU : x ≤ (819 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 2) (L := (739 / 500 : ℝ)) (U := (819 / 500 : ℝ))
    (alpha := (15900277 / 200000000 : ℝ)) (eta := (7950139 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B10 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (819 / 500 : ℝ) ≤ x) (hU : x ≤ (899 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 2) (L := (819 / 500 : ℝ)) (U := (899 / 500 : ℝ))
    (alpha := (31136599 / 250000000 : ℝ)) (eta := (155683 / 12500000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B11 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2249 / 1000 : ℝ) ≤ x) (hU : x ≤ (1173 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 2) (L := (2249 / 1000 : ℝ)) (U := (1173 / 500 : ℝ))
    (alpha := (5565687 / 62500000 : ℝ)) (eta := (89051 / 10000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B12 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1173 / 500 : ℝ) ≤ x) (hU : x ≤ (2443 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 2) (L := (1173 / 500 : ℝ)) (U := (2443 / 1000 : ℝ))
    (alpha := (15732181 / 250000000 : ℝ)) (eta := (6292873 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B13 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2443 / 1000 : ℝ) ≤ x) (hU : x ≤ (2637 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 3) (L := (2443 / 1000 : ℝ)) (U := (2637 / 1000 : ℝ))
    (alpha := (6929363 / 250000000 : ℝ)) (eta := (1385873 / 500000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B14 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1679 / 500 : ℝ) ≤ x) (hU : x ≤ (3463 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_left
    (N := 3) (L := (1679 / 500 : ℝ)) (U := (3463 / 1000 : ℝ))
    (alpha := (28459899 / 1000000000 : ℝ)) (eta := (284599 / 100000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B15 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (3463 / 1000 : ℝ) ≤ x) (hU : x ≤ (446 / 125 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 4) (L := (3463 / 1000 : ℝ)) (U := (446 / 125 : ℝ))
    (alpha := (8632019 / 500000000 : ℝ)) (eta := (431601 / 250000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B16 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (35 / 8 : ℝ) ≤ x) (hU : x ≤ (4493 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 5) (L := (35 / 8 : ℝ)) (U := (4493 / 1000 : ℝ))
    (alpha := (1729743 / 250000000 : ℝ)) (eta := (345949 / 500000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B17 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (4493 / 1000 : ℝ) ≤ x) (hU : x ≤ (4611 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_right
    (N := 5) (L := (4493 / 1000 : ℝ)) (U := (4611 / 1000 : ℝ))
    (alpha := (3002981 / 250000000 : ℝ)) (eta := (1201193 / 1000000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B18 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1057 / 200 : ℝ) ≤ x) (hU : x ≤ (21890 / 3733 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  apply v26_certified_onebody_stationary
    (N := 6) (L := (1057 / 200 : ℝ)) (U := (21890 / 3733 : ℝ))
    (alpha := (136767 / 62500000 : ℝ)) (eta := (54707 / 250000000000000 : ℝ))
    (p := (3733 / 10000000 : ℝ)) (target := (2189 / 1000000 : ℝ)) (c := (26233292691 / 4558900000 : ℝ))
    (by norm_num) (by norm_num) hx89 hL hU
  all_goals norm_num [v26CellLstar, v26CellEps, v26CellRho, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0]

theorem v26_excl_B_parent1 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (89 / 100 : ℝ) ≤ x) (hU : x ≤ (191 / 200 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_B01 hx89 hL hU

theorem v26_excl_B_parent2 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (579 / 500 : ℝ) ≤ x) (hU : x ≤ (899 / 500 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut02 : x ≤ (1163 / 1000 : ℝ)
  · exact v26_excl_B02 hx89 hL hcut02
  · have hL02 : (1163 / 1000 : ℝ) ≤ x := by linarith
    by_cases hcut03 : x ≤ (146 / 125 : ℝ)
    · exact v26_excl_B03 hx89 hL02 hcut03
    · have hL03 : (146 / 125 : ℝ) ≤ x := by linarith
      by_cases hcut04 : x ≤ (589 / 500 : ℝ)
      · exact v26_excl_B04 hx89 hL03 hcut04
      · have hL04 : (589 / 500 : ℝ) ≤ x := by linarith
        by_cases hcut05 : x ≤ (599 / 500 : ℝ)
        · exact v26_excl_B05 hx89 hL04 hcut05
        · have hL05 : (599 / 500 : ℝ) ≤ x := by linarith
          by_cases hcut06 : x ≤ (619 / 500 : ℝ)
          · exact v26_excl_B06 hx89 hL05 hcut06
          · have hL06 : (619 / 500 : ℝ) ≤ x := by linarith
            by_cases hcut07 : x ≤ (659 / 500 : ℝ)
            · exact v26_excl_B07 hx89 hL06 hcut07
            · have hL07 : (659 / 500 : ℝ) ≤ x := by linarith
              by_cases hcut08 : x ≤ (739 / 500 : ℝ)
              · exact v26_excl_B08 hx89 hL07 hcut08
              · have hL08 : (739 / 500 : ℝ) ≤ x := by linarith
                by_cases hcut09 : x ≤ (819 / 500 : ℝ)
                · exact v26_excl_B09 hx89 hL08 hcut09
                · have hL09 : (819 / 500 : ℝ) ≤ x := by linarith
                  exact v26_excl_B10 hx89 hL09 hU

theorem v26_excl_B_parent3 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (2249 / 1000 : ℝ) ≤ x) (hU : x ≤ (2637 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut11 : x ≤ (1173 / 500 : ℝ)
  · exact v26_excl_B11 hx89 hL hcut11
  · have hL11 : (1173 / 500 : ℝ) ≤ x := by linarith
    by_cases hcut12 : x ≤ (2443 / 1000 : ℝ)
    · exact v26_excl_B12 hx89 hL11 hcut12
    · have hL12 : (2443 / 1000 : ℝ) ≤ x := by linarith
      exact v26_excl_B13 hx89 hL12 hU

theorem v26_excl_B_parent4 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1679 / 500 : ℝ) ≤ x) (hU : x ≤ (446 / 125 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut14 : x ≤ (3463 / 1000 : ℝ)
  · exact v26_excl_B14 hx89 hL hcut14
  · have hL14 : (3463 / 1000 : ℝ) ≤ x := by linarith
    exact v26_excl_B15 hx89 hL14 hU

theorem v26_excl_B_parent5 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (35 / 8 : ℝ) ≤ x) (hU : x ≤ (4611 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  by_cases hcut16 : x ≤ (4493 / 1000 : ℝ)
  · exact v26_excl_B16 hx89 hL hcut16
  · have hL16 : (4493 / 1000 : ℝ) ≤ x := by linarith
    exact v26_excl_B17 hx89 hL16 hU

theorem v26_excl_B_parent6 {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hL : (1057 / 200 : ℝ) ≤ x) (hU : x ≤ (21890 / 3733 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  exact v26_excl_B18 hx89 hL hU

end HurtadoZeta23
