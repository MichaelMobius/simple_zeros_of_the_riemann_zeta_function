import HurtadoZeta23.V26OneBodyCellTools
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-! Canonical rational normalizations for the decimal-form basin endpoints.
They let the interface tables and the exact cell certificate share one simp-normal form. -/
@[simp] lemma v26_rat_955_1000 : (955 / 1000 : ℝ) = 191 / 200 := by norm_num
@[simp] lemma v26_rat_1158_1000 : (1158 / 1000 : ℝ) = 579 / 500 := by norm_num
@[simp] lemma v26_rat_1792_1000 : (1792 / 1000 : ℝ) = 224 / 125 := by norm_num
@[simp] lemma v26_rat_2258_1000 : (2258 / 1000 : ℝ) = 1129 / 500 := by norm_num
@[simp] lemma v26_rat_2612_1000 : (2612 / 1000 : ℝ) = 653 / 250 := by norm_num
@[simp] lemma v26_rat_3396_1000 : (3396 / 1000 : ℝ) = 849 / 250 := by norm_num
@[simp] lemma v26_rat_3502_1000 : (3502 / 1000 : ℝ) = 1751 / 500 := by norm_num
@[simp] lemma v26_rat_4465_1000 : (4465 / 1000 : ℝ) = 893 / 200 := by norm_num
@[simp] lemma v26_rat_4500_1000 : (4500 / 1000 : ℝ) = 9 / 2 := by norm_num
@[simp] lemma v26_rat_5466_1000 : (5466 / 1000 : ℝ) = 2733 / 500 := by norm_num
@[simp] lemma v26_rat_5500_1000 : (5500 / 1000 : ℝ) = 11 / 2 := by norm_num
@[simp] lemma v26_rat_6576_1000 : (6576 / 1000 : ℝ) = 822 / 125 := by norm_num
@[simp] lemma v26_rat_7270_1000 : (7270 / 1000 : ℝ) = 727 / 100 := by norm_num
@[simp] lemma v26_rat_1798_1000 : (1798 / 1000 : ℝ) = 899 / 500 := by norm_num
@[simp] lemma v26_rat_3358_1000 : (3358 / 1000 : ℝ) = 1679 / 500 := by norm_num
@[simp] lemma v26_rat_3568_1000 : (3568 / 1000 : ℝ) = 446 / 125 := by norm_num
@[simp] lemma v26_rat_4375_1000 : (4375 / 1000 : ℝ) = 35 / 8 := by norm_num
@[simp] lemma v26_rat_5285_1000 : (5285 / 1000 : ℝ) = 1057 / 200 := by norm_num
@[simp] lemma v26_rat_3365_1000 : (3365 / 1000 : ℝ) = 673 / 200 := by norm_num
@[simp] lemma v26_rat_3556_1000 : (3556 / 1000 : ℝ) = 889 / 250 := by norm_num
@[simp] lemma v26_rat_4392_1000 : (4392 / 1000 : ℝ) = 549 / 125 := by norm_num
@[simp] lemma v26_rat_4580_1000 : (4580 / 1000 : ℝ) = 229 / 50 := by norm_num
@[simp] lemma v26_rat_5322_1000 : (5322 / 1000 : ℝ) = 2661 / 500 := by norm_num
@[simp] lemma v26_rat_6078_1000 : (6078 / 1000 : ℝ) = 3039 / 500 := by norm_num

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
