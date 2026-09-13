import HurtadoZeta23.V26StrongConvexityLemma
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Transfer an absolute derivative enclosure and an absolute displacement
bound into the linear-error term used by the final strong-convexity table. -/
lemma v26_anchor_derivative_error_lower
    {fp D x a eps R : ℝ}
    (heps : 0 ≤ eps) (hR : 0 ≤ R)
    (hder : |fp - D| ≤ eps)
    (hdist : |x - a| ≤ R) :
    D * (x - a) - R * eps ≤ fp * (x - a) := by
  have hprod : |(fp - D) * (x - a)| ≤ eps * R := by
    rw [abs_mul]
    exact mul_le_mul hder hdist (abs_nonneg _) heps
  have hneg := neg_le_of_abs_le hprod
  nlinarith

/-- Generic final-table lower bound.  It combines a strong-convexity Taylor
bound at an anchor with rational lower data for the value and derivative. -/
theorem v26_strong_convex_table_lower
    {f fp fpp : ℝ → ℝ} {L U a x m W D eps R : ℝ}
    (ha : a ∈ Set.Icc L U) (hx : x ∈ Set.Icc L U)
    (hf : ∀ y ∈ Set.Icc L U, HasDerivAt f (fp y) y)
    (hfp : ∀ y ∈ Set.Icc L U, HasDerivAt fp (fpp y) y)
    (hm : ∀ y ∈ Set.Icc L U, m ≤ fpp y)
    (hW : W ≤ f a)
    (hD : |fp a - D| ≤ eps)
    (heps : 0 ≤ eps) (hR : 0 ≤ R)
    (hdist : |x - a| ≤ R) :
    W - R * eps + D * (x - a) + (m / 2) * (x - a) ^ 2 ≤ f x := by
  have htaylor := v26_strong_convex_taylor_lower ha hx hf hfp hm
  have herr := v26_anchor_derivative_error_lower
    (fp := fp a) (D := D) (x := x) (a := a)
    heps hR hD hdist
  nlinarith

/-- Specialization of the generic table lemma to the article's limiting
weight.  All transcendental information is exposed as three hypotheses:
curvature on the cell, the anchor-value floor, and the anchor-derivative
error.  Downstream generated modules therefore contain only rational cell
data. -/
theorem v26_limitingWeight_strong_lower
    {L U a x m W D eps R : ℝ}
    (hLhard : (89 / 100 : ℝ) < L)
    (ha : a ∈ Set.Icc L U) (hx : x ∈ Set.Icc L U)
    (hcurv : ∀ y ∈ Set.Icc L U, m ≤ v26WeightXSecond y)
    (hW : W ≤ limitingWeight a)
    (hDer : |v26WeightXPrime a - D| ≤ eps)
    (heps : 0 ≤ eps) (hR : 0 ≤ R)
    (hdist : |x - a| ≤ R) :
    W - R * eps + D * (x - a) + (m / 2) * (x - a) ^ 2 ≤
      limitingWeight x := by
  have hcert_of_mem : ∀ y ∈ Set.Icc L U, v17KernelCertPoint < y := by
    intro y hy
    have hy89 : (89 / 100 : ℝ) < y := hLhard.trans_le hy.1
    simpa [v17KernelCertPoint] using hy89
  have hf : ∀ y ∈ Set.Icc L U,
      HasDerivAt (fun z : ℝ => (v21KernelX z) ^ 2) (v26WeightXPrime y) y := by
    intro y hy
    have hA := v21_A_lt_B_of_cert_lt (hcert_of_mem y hy)
    have hDpos := v21_D_pos hA
    have hDneq : (v21B y) ^ 2 - (1 / 2 : ℝ) ≠ 0 := by
      simpa [v21D] using ne_of_gt hDpos
    exact v26_weightX_hasDerivAt hDneq
  have hfp : ∀ y ∈ Set.Icc L U,
      HasDerivAt v26WeightXPrime (v26WeightXSecond y) y := by
    intro y hy
    have hA := v21_A_lt_B_of_cert_lt (hcert_of_mem y hy)
    have hDpos := v21_D_pos hA
    have hDneq : (v21B y) ^ 2 - (1 / 2 : ℝ) ≠ 0 := by
      simpa [v21D] using ne_of_gt hDpos
    exact v26_weightXPrime_hasDerivAt hDneq
  have haCert := hcert_of_mem a ha
  have hxCert := hcert_of_mem x hx
  have hWsq : W ≤ (v21KernelX a) ^ 2 := by
    rw [← v26_limitingWeight_eq_kernelX_sq haCert]
    exact hW
  have hsq := v26_strong_convex_table_lower
    (f := fun z : ℝ => (v21KernelX z) ^ 2)
    (fp := v26WeightXPrime) (fpp := v26WeightXSecond)
    ha hx hf hfp hcurv hWsq hDer heps hR hdist
  rw [← v26_limitingWeight_eq_kernelX_sq hxCert] at hsq
  exact hsq

end HurtadoZeta23
