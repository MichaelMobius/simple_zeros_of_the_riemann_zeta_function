import HurtadoZeta23.V26OneBodyGlobalFloors
import HurtadoZeta23.V26OneBodyMicroA
import HurtadoZeta23.V26OneBodyMicroB
import HurtadoZeta23.V26OneBodyMicroC
import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- Package D micro-floor half of the basin interface, specialized to the article's limiting weight. -/
theorem v26_basin_micro_floors : V26BasinMicroFloorClaim limitingWeight := by
  constructor
  · intro i x hi
    fin_cases i
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A1 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A2 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A3 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A4 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A5 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A6 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InA, v26ALo, v26AHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_A7 (x := x) hx89 hL hU
      norm_num [v26MuA, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
  constructor
  · intro i x hi
    fin_cases i
    · norm_num [v26InB, v26BLo, v26BHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_B1 (x := x) hx89 hL hU
      norm_num [v26MuB, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InB, v26BLo, v26BHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_B2 (x := x) hx89 hL hU
      norm_num [v26MuB, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InB, v26BLo, v26BHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_B3 (x := x) hx89 hL hU
      norm_num [v26MuB, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InB, v26BLo, v26BHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_B4 (x := x) hx89 hL hU
      norm_num [v26MuB, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InB, v26BLo, v26BHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_B5 (x := x) hx89 hL hU
      norm_num [v26MuB, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
  · intro i x hi
    fin_cases i
    · norm_num [v26InC, v26CLo, v26CHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_C1 (x := x) hx89 hL hU
      norm_num [v26MuC, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InC, v26CLo, v26CHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_C2 (x := x) hx89 hL hU
      norm_num [v26MuC, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InC, v26CLo, v26CHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_C3 (x := x) hx89 hL hU
      norm_num [v26MuC, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InC, v26CLo, v26CHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_C4 (x := x) hx89 hL hU
      norm_num [v26MuC, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InC, v26CLo, v26CHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_C5 (x := x) hx89 hL hU
      norm_num [v26MuC, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm
    · norm_num [v26InC, v26CLo, v26CHi, Matrix.cons_val_succ'] at hi
      rcases hi with ⟨hL, hU⟩
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      have hm := v26_micro_C6 (x := x) hx89 hL hU
      norm_num [v26MuC, v26Pressure, Matrix.cons_val_succ'] at hm ⊢
      exact hm

end HurtadoZeta23
