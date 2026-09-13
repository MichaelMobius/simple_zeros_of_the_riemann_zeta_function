import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- Compact Package-D wrapper for a certified cell whose quadratic minimum
is attained at the left endpoint. -/
theorem v26_certified_onebody_left
    {N : ℕ} {L U x alpha eta p target : ℝ}
    (hN1 : 1 ≤ N) (hN12 : N ≤ 12)
    (hx89 : (89 / 100 : ℝ) < x)
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < v26CellLstar L N)
    (hrho0 : 0 < v26CellRho L U N)
    (hrho1 : v26CellRho L U N < 1)
    (halpha : alpha ≤ (999 / 1000 : ℝ) * v26Araw U (v26CellRho L U N))
    (heta : (999 / 10000000000 : ℝ) * v26Araw U (v26CellRho L U N) ≤ eta)
    (ha : 0 ≤ alpha / 3)
    (hder : 0 ≤ p + 2 * (alpha / 3) * (L - v21RootRight N))
    (hmin : target ≤ p * L + (alpha / 3) * (L - v21RootRight N) ^ 2 - eta / 3) :
    target ≤ p * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := N) (L := L) (U := U) (x := x)
    (alpha := alpha) (eta := eta)
    hN1 hN12 hx89 hLx hxU hLstar0 hrho0 hrho1 halpha heta
  have hq := v26_quad_lower_left
    (p := p) (a := alpha / 3) (q := v21RootRight N)
    (eta := eta / 3) (L := L) ha hLx hder hmin
  apply v26_oneBody_lower_of_minorant hminor
  convert hq using 1 <;> ring

/-- Compact Package-D wrapper for a certified cell whose quadratic minimum
is attained at the right endpoint. -/
theorem v26_certified_onebody_right
    {N : ℕ} {L U x alpha eta p target : ℝ}
    (hN1 : 1 ≤ N) (hN12 : N ≤ 12)
    (hx89 : (89 / 100 : ℝ) < x)
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < v26CellLstar L N)
    (hrho0 : 0 < v26CellRho L U N)
    (hrho1 : v26CellRho L U N < 1)
    (halpha : alpha ≤ (999 / 1000 : ℝ) * v26Araw U (v26CellRho L U N))
    (heta : (999 / 10000000000 : ℝ) * v26Araw U (v26CellRho L U N) ≤ eta)
    (ha : 0 ≤ alpha / 3)
    (hder : p + 2 * (alpha / 3) * (U - v21RootRight N) ≤ 0)
    (hmin : target ≤ p * U + (alpha / 3) * (U - v21RootRight N) ^ 2 - eta / 3) :
    target ≤ p * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := N) (L := L) (U := U) (x := x)
    (alpha := alpha) (eta := eta)
    hN1 hN12 hx89 hLx hxU hLstar0 hrho0 hrho1 halpha heta
  have hq := v26_quad_lower_right
    (p := p) (a := alpha / 3) (q := v21RootRight N)
    (eta := eta / 3) (U := U) ha hxU hder hmin
  apply v26_oneBody_lower_of_minorant hminor
  convert hq using 1 <;> ring

/-- Compact Package-D wrapper for a certified cell whose quadratic stationary
point is explicitly supplied. -/
theorem v26_certified_onebody_stationary
    {N : ℕ} {L U x alpha eta p target c : ℝ}
    (hN1 : 1 ≤ N) (hN12 : N ≤ 12)
    (hx89 : (89 / 100 : ℝ) < x)
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < v26CellLstar L N)
    (hrho0 : 0 < v26CellRho L U N)
    (hrho1 : v26CellRho L U N < 1)
    (halpha : alpha ≤ (999 / 1000 : ℝ) * v26Araw U (v26CellRho L U N))
    (heta : (999 / 10000000000 : ℝ) * v26Araw U (v26CellRho L U N) ≤ eta)
    (ha : 0 ≤ alpha / 3)
    (hstat : p + 2 * (alpha / 3) * (c - v21RootRight N) = 0)
    (hmin : target ≤ p * c + (alpha / 3) * (c - v21RootRight N) ^ 2 - eta / 3) :
    target ≤ p * x + (1 / 3 : ℝ) * limitingWeight x := by
  have hminor := v26_certified_cell_minorant
    (N := N) (L := L) (U := U) (x := x)
    (alpha := alpha) (eta := eta)
    hN1 hN12 hx89 hLx hxU hLstar0 hrho0 hrho1 halpha heta
  have hq := v26_quad_lower_stationary
    (p := p) (a := alpha / 3) (q := v21RootRight N)
    (eta := eta / 3) (c := c) ha hstat hmin
  apply v26_oneBody_lower_of_minorant hminor
  convert hq using 1 <;> ring

end HurtadoZeta23
