import HurtadoZeta23.V26CertifiedPhaseRoots
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The fixed rational root-radius used by every v26 one-body cell. -/
def v26CellEps : ℝ := 1 / 100000

/-- Safe positive lower endpoint used by the certified phase minorant. -/
def v26CellLstar (L : ℝ) (N : ℕ) : ℝ :=
  min L (v21RootRight N - v26CellEps)

/-- Exact rational phase radius attached to a one-dimensional cell. -/
def v26CellRho (L U : ℝ) (N : ℕ) : ℝ :=
  v26Mrat (v26CellLstar L N) *
    (max |L - v21RootRight N| |U - v21RootRight N| + v26CellEps)

/-- The article's limiting weight is a square, hence nonnegative everywhere. -/
theorem v26_limitingWeight_nonneg (x : ℝ) : 0 ≤ limitingWeight x := by
  unfold limitingWeight
  positivity

/-- Every point in the strict hard core lies beyond the removable singularity
of the closed-form kernel. -/
lemma v26_A_lt_B_of_hardcore {x : ℝ} (hx : (89 / 100 : ℝ) < x) :
    v21A < v21B x := by
  apply v21_A_lt_B_of_cert_lt
  simpa [v17KernelCertPoint] using hx

/-- On the strict hard core the exact denominator constant lies below `x^2`. -/
lemma v26_dk_lt_sq_of_hardcore {x : ℝ} (hx : (89 / 100 : ℝ) < x) :
    v26dk < x ^ 2 := by
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hden : (18 : ℝ) < 2 * Real.pi ^ 2 := by
    nlinarith
  have hrec : 1 / (2 * Real.pi ^ 2) < (1 / 18 : ℝ) := by
    exact one_div_lt_one_div_of_lt (by norm_num) hden
  have hx2 : (1 / 18 : ℝ) < x ^ 2 := by
    nlinarith
  simpa [v26dk] using hrec.trans hx2

/-- V26-native wrapper for one fixed rational cell.  All transcendental work
is delegated to Package C and the analytic minorant from Package A.  Callers
only discharge rational inequalities for `Lstar`, `rho`, `alpha`, and `eta`. -/
theorem v26_certified_cell_minorant
    {N : ℕ} {L U x alpha eta : ℝ}
    (hN1 : 1 ≤ N) (hN12 : N ≤ 12)
    (hx89 : (89 / 100 : ℝ) < x)
    (hLx : L ≤ x) (hxU : x ≤ U)
    (hLstar0 : 0 < v26CellLstar L N)
    (hrho0 : 0 < v26CellRho L U N)
    (hrho1 : v26CellRho L U N < 1)
    (halpha : alpha ≤
      (999 / 1000 : ℝ) * v26Araw U (v26CellRho L U N))
    (heta :
      (999 / 10000000000 : ℝ) * v26Araw U (v26CellRho L U N) ≤ eta) :
    alpha * (x - v21RootRight N) ^ 2 - eta ≤ limitingWeight x := by
  have hLstarx : v26CellLstar L N ≤ x := by
    unfold v26CellLstar
    exact (min_le_left _ _).trans hLx
  exact v26_rounded_cell_minorant_certified
    (N := N) (L := L) (U := U)
    (Lstar := v26CellLstar L N) (x := x)
    (q := v21RootRight N) (eps := v26CellEps)
    (rho := v26CellRho L U N) (alpha := alpha) (eta := eta)
    hN1 hN12 rfl rfl rfl hLx hxU hLstar0 hLstarx rfl
    hrho0 hrho1 (v26_A_lt_B_of_hardcore hx89)
    (v26_dk_lt_sq_of_hardcore hx89) halpha heta

end HurtadoZeta23
