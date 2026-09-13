import HurtadoZeta23.V21KernelRootBracketsLow
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Left endpoint certificate for kernel zero 6. -/
lemma v21_rootH_six_left :
    v21RootH 6 (601018 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 6 (601018 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (601018 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (1018 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (1018 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 6) (x := (601018 / 100000 : ℝ))
        (e := (1018 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 6. -/
lemma v21_rootH_six_right :
    (1 / 100000 : ℝ) ≤ v21RootH 6 (601019 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (601019 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (1019 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (1019 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 6 (601019 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 6) (x := (601019 / 100000 : ℝ))
        (e := (1019 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 7. -/
lemma v21_rootH_seven_left :
    v21RootH 7 (700873 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 7 (700873 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (700873 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (873 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (873 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 7) (x := (700873 / 100000 : ℝ))
        (e := (873 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 7. -/
lemma v21_rootH_seven_right :
    (1 / 100000 : ℝ) ≤ v21RootH 7 (700874 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (700874 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (874 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (874 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 7 (700874 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 7) (x := (700874 / 100000 : ℝ))
        (e := (874 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 8. -/
lemma v21_rootH_eight_left :
    v21RootH 8 (800764 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 8 (800764 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (800764 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (764 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (764 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 8) (x := (800764 / 100000 : ℝ))
        (e := (764 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 8. -/
lemma v21_rootH_eight_right :
    (1 / 100000 : ℝ) ≤ v21RootH 8 (800765 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (800765 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (765 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (765 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 8 (800765 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 8) (x := (800765 / 100000 : ℝ))
        (e := (765 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 9. -/
lemma v21_rootH_nine_left :
    v21RootH 9 (900679 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 9 (900679 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (900679 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (679 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (679 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 9) (x := (900679 / 100000 : ℝ))
        (e := (679 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 9. -/
lemma v21_rootH_nine_right :
    (1 / 100000 : ℝ) ≤ v21RootH 9 (900680 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (900680 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (680 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (680 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 9 (900680 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 9) (x := (900680 / 100000 : ℝ))
        (e := (680 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

end HurtadoZeta23
