import HurtadoZeta23.V17AnalyticBridge450
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The normalized ordinates in an actual v17 block are nondecreasing.  This is
an immediate specialization of `orderedRetainedY_mono`; no new analytic input
is required beyond nonnegativity of the scaling factor `articleParams.L T`. -/
theorem v17Y450_mono
    {T : ℝ}
    (hL : 0 ≤ articleParams.L T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    ∀ q < 449, v17Y450 T s hs q ≤ v17Y450 T s hs (q + 1) := by
  intro q hq
  have hq0 : q < 450 := by omega
  have hq1 : q + 1 < 450 := by omega
  rw [v17Y450_of_lt T s hs hq0]
  rw [v17Y450_of_lt T s hs hq1]
  apply orderedRetainedY_mono hL
  change s + q ≤ s + (q + 1)
  omega

end HurtadoZeta23
