import Zeta23.ThmD.Mult
import HurtadoZeta23.Constants
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section

open Filter Asymptotics

namespace HurtadoZeta23

/-- The actual dyadic zero count used throughout the refinement. -/
def zetaDyadicN (T : ℝ) : ℝ :=
  (Zeta23.Ncount T (2 * T) : ℝ)

lemma zetaDyadicN_nonneg (T : ℝ) :
    0 ≤ zetaDyadicN T := by
  simp [zetaDyadicN]

/-- Riemann--von Mangoldt from Zeta23 implies that the dyadic zero count
tends to infinity. -/
theorem zetaDyadicN_tendsto_atTop :
    Tendsto zetaDyadicN atTop atTop := by
  change Tendsto
    (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ))
    atTop atTop
  exact Zeta23.Assembly.tendsto_N_atTop
    Zeta23.zetaZeroConfig
    Zeta23.paperInputs_zeta.RvM

/-- Hence `1 = o(N(T,2T))`. -/
theorem one_isLittleO_zetaDyadicN :
    (fun _ : ℝ => (1 : ℝ)) =o[atTop] zetaDyadicN := by
  rw [Asymptotics.isLittleO_one_left_iff]
  have h := zetaDyadicN_tendsto_atTop
  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg (zetaDyadicN_nonneg _)
  ] using h

/-- Every fixed real constant is `o(N(T,2T))`. -/
theorem const_isLittleO_zetaDyadicN (c : ℝ) :
    (fun _ : ℝ => c) =o[atTop] zetaDyadicN := by
  simpa using
    (one_isLittleO_zetaDyadicN.const_mul_left c)

/-- The fixed shifted-pinching endpoint correction is negligible. -/
theorem endpointCorrection_isLittleO_zetaDyadicN :
    (fun _ : ℝ => endpointCorrection) =o[atTop] zetaDyadicN := by
  exact const_isLittleO_zetaDyadicN endpointCorrection

end HurtadoZeta23
