import HurtadoZeta23.V26OneBodyCellTools
import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Prototype for the first published type-A micro-floor.  This exercises the
full Package A + Package C certified-cell path with only rational side goals. -/
theorem v26_micro_A1 {x : ℝ}
    (hL : (955 / 1000 : ℝ) ≤ x) (hU : x ≤ (1158 / 1000 : ℝ)) :
    (286 / 1000000 : ℝ) ≤
      (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hx89 : (89 / 100 : ℝ) < x := by nlinarith
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
      (286 / 1000000 : ℝ) ≤
        (2714 / 10000000 : ℝ) * x +
          (1 / 3 : ℝ) *
            ((13219307 / 25000000 : ℝ) *
                (x - v21RootRight 1) ^ 2 -
              (52877229 / 1000000000000000 : ℝ)) := by
    apply v26_quad_lower_stationary
      (p := (2714 / 10000000 : ℝ))
      (a := (13219307 / 75000000 : ℝ))
      (q := v21RootRight 1)
      (eta := (52877229 / 3000000000000000 : ℝ))
      (c := (87289571281 / 82620668750 : ℝ))
    · norm_num
    · norm_num [v21RootRight]
    · norm_num [v21RootRight]
  exact v26_oneBody_lower_of_minorant hminor hquad

end HurtadoZeta23
