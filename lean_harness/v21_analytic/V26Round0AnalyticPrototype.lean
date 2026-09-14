import HurtadoZeta23.V26Round0Prototype
import HurtadoZeta23.V26OneBodyCellTools
import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- The concrete A-B-C-C-B-A word with published code `111114`. -/
def v26Word111114 : V26BasinWord :=
  ((0 : Fin 7), (0 : Fin 5), (0 : Fin 6), (0 : Fin 6), (0 : Fin 5), (3 : Fin 7))

private lemma v26_R0_111114_minor_1 {x : ℝ}
    (hL : (955 / 1000 : ℝ) ≤ x) (hU : x ≤ (1158 / 1000 : ℝ)) :
    (13219307 / 25000000 : ℝ) * (x - (105728 / 100000 : ℝ)) ^ 2 -
      (52877229 / 1000000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 1) (L := (955 / 1000 : ℝ)) (U := (1158 / 1000 : ℝ))
    (alpha := (13219307 / 25000000 : ℝ))
    (eta := (52877229 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_4a {x : ℝ}
    (hL : (3502 / 1000 : ℝ) ≤ x) (hU : x ≤ (4465 / 1000 : ℝ)) :
    (1308653 / 100000000 : ℝ) * (x - (401524 / 100000 : ℝ)) ^ 2 -
      (654327 / 500000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 4) (L := (3502 / 1000 : ℝ)) (U := (4465 / 1000 : ℝ))
    (alpha := (1308653 / 100000000 : ℝ))
    (eta := (654327 / 500000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_2 {x : ℝ}
    (hL : (1910 / 1000 : ℝ) ≤ x) (hU : x ≤ (2316 / 1000 : ℝ)) :
    (4873609 / 50000000 : ℝ) * (x - (203007 / 100000 : ℝ)) ^ 2 -
      (9747219 / 1000000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 2) (L := (1910 / 1000 : ℝ)) (U := (2316 / 1000 : ℝ))
    (alpha := (4873609 / 50000000 : ℝ))
    (eta := (9747219 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_5a {x : ℝ}
    (hL : (4457 / 1000 : ℝ) ≤ x) (hU : x ≤ (5623 / 1000 : ℝ)) :
    (5147787 / 1000000000 : ℝ) * (x - (501221 / 100000 : ℝ)) ^ 2 -
      (514779 / 1000000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 5) (L := (4457 / 1000 : ℝ)) (U := (5623 / 1000 : ℝ))
    (alpha := (5147787 / 1000000000 : ℝ))
    (eta := (514779 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_3 {x : ℝ}
    (hL : (2865 / 1000 : ℝ) ≤ x) (hU : x ≤ (3474 / 1000 : ℝ)) :
    (27182511 / 1000000000 : ℝ) * (x - (302025 / 100000 : ℝ)) ^ 2 -
      (679563 / 250000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 3) (L := (2865 / 1000 : ℝ)) (U := (3474 / 1000 : ℝ))
    (alpha := (27182511 / 1000000000 : ℝ))
    (eta := (679563 / 250000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_6 {x : ℝ}
    (hL : (5412 / 1000 : ℝ) ≤ x) (hU : x ≤ (6781 / 1000 : ℝ)) :
    (1086317 / 1000000000 : ℝ) * (x - (601019 / 100000 : ℝ)) ^ 2 -
      (13579 / 125000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 6) (L := (5412 / 1000 : ℝ)) (U := (6781 / 1000 : ℝ))
    (alpha := (1086317 / 1000000000 : ℝ))
    (eta := (13579 / 125000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_4b {x : ℝ}
    (hL : (3820 / 1000 : ℝ) ≤ x) (hU : x ≤ (4632 / 1000 : ℝ)) :
    (7316501 / 1000000000 : ℝ) * (x - (401524 / 100000 : ℝ)) ^ 2 -
      (731651 / 1000000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 4) (L := (3820 / 1000 : ℝ)) (U := (4632 / 1000 : ℝ))
    (alpha := (7316501 / 1000000000 : ℝ))
    (eta := (731651 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_7 {x : ℝ}
    (hL : (6367 / 1000 : ℝ) ≤ x) (hU : x ≤ (7939 / 1000 : ℝ)) :
    (57461 / 1000000000 : ℝ) * (x - (700874 / 100000 : ℝ)) ^ 2 -
      (5747 / 1000000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 7) (L := (6367 / 1000 : ℝ)) (U := (7939 / 1000 : ℝ))
    (alpha := (57461 / 1000000000 : ℝ))
    (eta := (5747 / 1000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

private lemma v26_R0_111114_minor_5b {x : ℝ}
    (hL : (4775 / 1000 : ℝ) ≤ x) (hU : x ≤ (5790 / 1000 : ℝ)) :
    (692067 / 500000000 : ℝ) * (x - (501221 / 100000 : ℝ)) ^ 2 -
      (69207 / 500000000000000 : ℝ) ≤ limitingWeight x := by
  have h := v26_certified_cell_minorant
    (N := 5) (L := (4775 / 1000 : ℝ)) (U := (5790 / 1000 : ℝ))
    (alpha := (692067 / 500000000 : ℝ))
    (eta := (69207 / 500000000000000 : ℝ))
    (by norm_num) (by norm_num) (by linarith) hL hU
    (by norm_num [v26CellLstar, v26CellEps, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
    (by norm_num [v26CellRho, v26CellLstar, v26CellEps, v26Mrat, v21RootRight,
      v26Araw, v26AmplitudeFloor, v26ChordCoeff, v26Fold, v26P7, v26d0])
  simpa [v21RootRight] using h

/-- The rounded R0 quadratic for `111114` is an analytic lower bound for the
actual six-gap functional throughout its Package-D basin box. -/
theorem v26_R0_111114_Q_le_gapF
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26Word111114 x0 x1 x2 x3 x4 x5) :
    v26R0Q111114 x0 x1 x2 x3 x4 x5 ≤
      v26GapF limitingWeight x0 x1 x2 x3 x4 x5 := by
  change
    ((955 / 1000 : ℝ) ≤ x0 ∧ x0 ≤ (1158 / 1000 : ℝ)) ∧
    ((955 / 1000 : ℝ) ≤ x1 ∧ x1 ≤ (1158 / 1000 : ℝ)) ∧
    ((955 / 1000 : ℝ) ≤ x2 ∧ x2 ≤ (1158 / 1000 : ℝ)) ∧
    ((955 / 1000 : ℝ) ≤ x3 ∧ x3 ≤ (1158 / 1000 : ℝ)) ∧
    ((955 / 1000 : ℝ) ≤ x4 ∧ x4 ≤ (1158 / 1000 : ℝ)) ∧
    ((3502 / 1000 : ℝ) ≤ x5 ∧ x5 ≤ (4465 / 1000 : ℝ)) at hbox
  rcases hbox with ⟨h0, h1, h2, h3, h4, h5⟩
  have hm0 := v26_R0_111114_minor_1 h0.1 h0.2
  have hm1 := v26_R0_111114_minor_1 h1.1 h1.2
  have hm2 := v26_R0_111114_minor_1 h2.1 h2.2
  have hm3 := v26_R0_111114_minor_1 h3.1 h3.2
  have hm4 := v26_R0_111114_minor_1 h4.1 h4.2
  have hm5 := v26_R0_111114_minor_4a h5.1 h5.2
  have hm01 := v26_R0_111114_minor_2 (by linarith [h0.1, h1.1]) (by linarith [h0.2, h1.2])
  have hm12 := v26_R0_111114_minor_2 (by linarith [h1.1, h2.1]) (by linarith [h1.2, h2.2])
  have hm23 := v26_R0_111114_minor_2 (by linarith [h2.1, h3.1]) (by linarith [h2.2, h3.2])
  have hm34 := v26_R0_111114_minor_2 (by linarith [h3.1, h4.1]) (by linarith [h3.2, h4.2])
  have hm45 := v26_R0_111114_minor_5a (by linarith [h4.1, h5.1]) (by linarith [h4.2, h5.2])
  have hm012 := v26_R0_111114_minor_3 (by linarith [h0.1, h1.1, h2.1]) (by linarith [h0.2, h1.2, h2.2])
  have hm123 := v26_R0_111114_minor_3 (by linarith [h1.1, h2.1, h3.1]) (by linarith [h1.2, h2.2, h3.2])
  have hm234 := v26_R0_111114_minor_3 (by linarith [h2.1, h3.1, h4.1]) (by linarith [h2.2, h3.2, h4.2])
  have hm345 := v26_R0_111114_minor_6 (by linarith [h3.1, h4.1, h5.1]) (by linarith [h3.2, h4.2, h5.2])
  have hm0123 := v26_R0_111114_minor_4b (by linarith [h0.1, h1.1, h2.1, h3.1]) (by linarith [h0.2, h1.2, h2.2, h3.2])
  have hm1234 := v26_R0_111114_minor_4b (by linarith [h1.1, h2.1, h3.1, h4.1]) (by linarith [h1.2, h2.2, h3.2, h4.2])
  have hm2345 := v26_R0_111114_minor_7 (by linarith [h2.1, h3.1, h4.1, h5.1]) (by linarith [h2.2, h3.2, h4.2, h5.2])
  have hm01234 := v26_R0_111114_minor_5b
    (by linarith [h0.1, h1.1, h2.1, h3.1, h4.1])
    (by linarith [h0.2, h1.2, h2.2, h3.2, h4.2])
  have h12345 := v26_limitingWeight_nonneg (x1 + x2 + x3 + x4 + x5)
  have h012345 := v26_limitingWeight_nonneg (x0 + x1 + x2 + x3 + x4 + x5)
  unfold v26R0Q111114 v26GapF
  norm_num [v26Pressure, Matrix.cons_val_succ']
  linarith [hm0, hm1, hm2, hm3, hm4, hm5, hm01, hm12, hm23, hm34, hm45,
    hm012, hm123, hm234, hm345, hm0123, hm1234, hm2345, hm01234,
    h12345, h012345]

/-- The discarded word `111114` therefore cannot contain a strict
counterexample to the six-gap target. -/
theorem v26_R0_111114_no_counterexample
    (x0 x1 x2 x3 x4 x5 : ℝ)
    (hbox : v26InWordBox v26Word111114 x0 x1 x2 x3 x4 x5) :
    ¬ v26GapF limitingWeight x0 x1 x2 x3 x4 x5 < v26Delta := by
  intro hbad
  have hdom := v26_R0_111114_Q_le_gapF x0 x1 x2 x3 x4 x5 hbox
  have hdiscard := v26_R0_111114_discard x0 x1 x2 x3 x4 x5
  linarith

end HurtadoZeta23
