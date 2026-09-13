import HurtadoZeta23.V21KernelRootBrackets
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Left endpoint certificate for kernel zero 2. -/
lemma v21_rootH_two_left :
    v21RootH 2 (203006 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 2 (203006 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (203006 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (3006 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (3006 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 2) (x := (203006 / 100000 : ℝ))
        (e := (3006 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 2. -/
lemma v21_rootH_two_right :
    (1 / 100000 : ℝ) ≤ v21RootH 2 (203007 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (203007 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (3007 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (3007 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 2 (203007 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 2) (x := (203007 / 100000 : ℝ))
        (e := (3007 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 3. -/
lemma v21_rootH_three_left :
    v21RootH 3 (302024 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 3 (302024 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (302024 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (2024 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (2024 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 3) (x := (302024 / 100000 : ℝ))
        (e := (2024 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 3. -/
lemma v21_rootH_three_right :
    (1 / 100000 : ℝ) ≤ v21RootH 3 (302025 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (302025 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (2025 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (2025 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 3 (302025 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 3) (x := (302025 / 100000 : ℝ))
        (e := (2025 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 4. -/
lemma v21_rootH_four_left :
    v21RootH 4 (401523 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 4 (401523 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (401523 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (1523 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (1523 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 4) (x := (401523 / 100000 : ℝ))
        (e := (1523 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 4. -/
lemma v21_rootH_four_right :
    (1 / 100000 : ℝ) ≤ v21RootH 4 (401524 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (401524 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (1524 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (1524 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 4 (401524 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 4) (x := (401524 / 100000 : ℝ))
        (e := (1524 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

/-- Left endpoint certificate for kernel zero 5. -/
lemma v21_rootH_five_left :
    v21RootH 5 (501220 / 100000 : ℝ) ≤ -(7 / 100000 : ℝ) := by
  calc
    v21RootH 5 (501220 / 100000 : ℝ) ≤
        v21RootCU * v21RootPiU * (501220 / 100000 : ℝ) *
            v21RootSinUpper9 (v21RootPiU * (1220 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosLower10 (v21RootPiU * (1220 / 100000 : ℝ)) := by
      exact v21_rootH_upper_bound
        (n := 5) (x := (501220 / 100000 : ℝ))
        (e := (1220 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])
    _ ≤ -(7 / 100000 : ℝ) := by
      norm_num [v21RootCU, v21RootPiU, v21RootSinUpper9,
        v21RootCosLower10]

/-- Right endpoint certificate for kernel zero 5. -/
lemma v21_rootH_five_right :
    (1 / 100000 : ℝ) ≤ v21RootH 5 (501221 / 100000 : ℝ) := by
  calc
    (1 / 100000 : ℝ) ≤
        v21RootCL * v21RootPiL * (501221 / 100000 : ℝ) *
            v21RootSinLower7 (v21RootPiL * (1221 / 100000 : ℝ)) -
          (1 / 2 : ℝ) *
            v21RootCosUpper8 (v21RootPiL * (1221 / 100000 : ℝ)) := by
      norm_num [v21RootCL, v21RootPiL, v21RootSinLower7,
        v21RootCosUpper8]
    _ ≤ v21RootH 5 (501221 / 100000 : ℝ) := by
      exact v21_rootH_lower_bound
        (n := 5) (x := (501221 / 100000 : ℝ))
        (e := (1221 / 100000 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num [v21RootPiU])

end HurtadoZeta23
