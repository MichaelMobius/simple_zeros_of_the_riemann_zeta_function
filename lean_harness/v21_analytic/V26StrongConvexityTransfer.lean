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

end HurtadoZeta23
