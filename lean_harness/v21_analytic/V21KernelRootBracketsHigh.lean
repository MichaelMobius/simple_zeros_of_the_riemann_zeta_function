import HurtadoZeta23.V21KernelRootBracketsMid
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Left endpoint certificate for kernel zero 10. -/
lemma v21_rootH_ten_left :
    v21RootH 10 (1000611 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 10 (1000611 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (1000611 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (611 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (611 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 10) (x := (1000611 / 100000 : ℝ))
        (e := (611 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 10. -/
lemma v21_rootH_ten_right :
    (1 / 100000 : ℝ) ≤ v21RootH 10 (1000612 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (1000612 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (612 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (612 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 10 (1000612 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 10) (x := (1000612 / 100000 : ℝ))
        (e := (612 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 11. -/
lemma v21_rootH_eleven_left :
    v21RootH 11 (1100556 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 11 (1100556 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (1100556 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (556 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (556 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 11) (x := (1100556 / 100000 : ℝ))
        (e := (556 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 11. -/
lemma v21_rootH_eleven_right :
    (1 / 100000 : ℝ) ≤ v21RootH 11 (1100557 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (1100557 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (557 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (557 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 11 (1100557 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 11) (x := (1100557 / 100000 : ℝ))
        (e := (557 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 12. -/
lemma v21_rootH_twelve_left :
    v21RootH 12 (1200509 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 12 (1200509 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (1200509 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (509 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (509 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 12) (x := (1200509 / 100000 : ℝ))
        (e := (509 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 12. -/
lemma v21_rootH_twelve_right :
    (1 / 100000 : ℝ) ≤ v21RootH 12 (1200510 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (1200510 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (510 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (510 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 12 (1200510 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 12) (x := (1200510 / 100000 : ℝ))
        (e := (510 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

end HurtadoZeta23
