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
    · rcases hi with ⟨hL, hU⟩
      change (191 / 200 : ℝ) ≤ x at hL
      change x ≤ (579 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A1 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (224 / 125 : ℝ) ≤ x at hL
      change x ≤ (1129 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A2 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (653 / 250 : ℝ) ≤ x at hL
      change x ≤ (849 / 250 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A3 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (1751 / 500 : ℝ) ≤ x at hL
      change x ≤ (893 / 200 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A4 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (9 / 2 : ℝ) ≤ x at hL
      change x ≤ (2733 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A5 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (11 / 2 : ℝ) ≤ x at hL
      change x ≤ (6413 / 1000 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A6 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (822 / 125 : ℝ) ≤ x at hL
      change x ≤ (727 / 100 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuA, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_A7 (x := x) hx89 hL hU)
  constructor
  · intro i x hi
    fin_cases i
    · rcases hi with ⟨hL, hU⟩
      change (191 / 200 : ℝ) ≤ x at hL
      change x ≤ (579 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuB, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_B1 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (899 / 500 : ℝ) ≤ x at hL
      change x ≤ (2249 / 1000 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuB, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_B2 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (2637 / 1000 : ℝ) ≤ x at hL
      change x ≤ (1679 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuB, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_B3 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (446 / 125 : ℝ) ≤ x at hL
      change x ≤ (35 / 8 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuB, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_B4 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (4611 / 1000 : ℝ) ≤ x at hL
      change x ≤ (1057 / 200 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuB, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_B5 (x := x) hx89 hL hU)
  · intro i x hi
    fin_cases i
    · rcases hi with ⟨hL, hU⟩
      change (191 / 200 : ℝ) ≤ x at hL
      change x ≤ (579 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuC, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_C1 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (1797 / 1000 : ℝ) ≤ x at hL
      change x ≤ (2251 / 1000 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuC, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_C2 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (2633 / 1000 : ℝ) ≤ x at hL
      change x ≤ (673 / 200 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuC, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_C3 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (889 / 250 : ℝ) ≤ x at hL
      change x ≤ (549 / 125 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuC, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_C4 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (229 / 50 : ℝ) ≤ x at hL
      change x ≤ (2661 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuC, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_C5 (x := x) hx89 hL hU)
    · rcases hi with ⟨hL, hU⟩
      change (5793 / 1000 : ℝ) ≤ x at hL
      change x ≤ (3039 / 500 : ℝ) at hU
      have hx89 : (89 / 100 : ℝ) < x := by nlinarith
      simpa [v26MuC, v26Pressure, Matrix.cons_val_succ'] using
        (v26_micro_C6 (x := x) hx89 hL hU)

end HurtadoZeta23
