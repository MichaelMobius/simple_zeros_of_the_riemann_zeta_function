import HurtadoZeta23.V26RationalBall
import HurtadoZeta23.V26LocalClosedForms
import HurtadoZeta23.V26TrigIntervalBridge
import HurtadoZeta23.V21KernelRootBrackets
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Tight rational centre-radius certificate for π. -/
theorem v26_pi_ball :
    v26Ball Real.pi
      ((v21RootPiL + v21RootPiU) / 2)
      ((v21RootPiU - v21RootPiL) / 2) := by
  apply v26_ball_of_bounds
  · exact le_of_lt v21_pi_lower
  · exact le_of_lt v21_pi_upper

/-- Tight rational centre-radius certificate for the normalized profile
constant C. -/
theorem v26_C_ball :
    v26Ball v21C
      ((v21RootCL + v21RootCU) / 2)
      ((v21RootCU - v21RootCL) / 2) := by
  apply v26_ball_of_bounds
  · simpa [v21RootCL] using v21_C_lower
  · simpa [v21RootCU] using v21_C_upper

/-- Turn constant lower/upper bounds for the two sine Taylor polynomials into
an actual rational enclosure for sine. -/
lemma v26_sin_ball_of_taylor_bounds {u slo shi : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hlo : slo ≤ v21RootSinLower7 u)
    (hhi : v21RootSinUpper9 u ≤ shi) :
    v26Ball (Real.sin u) ((slo + shi) / 2) ((shi - slo) / 2) := by
  have hlowTaylor : v21RootSinLower7 u ≤ Real.sin u := by
    simpa [v21RootSinLower7] using v21_sin_lower7 hu0 hu1
  have hhighTaylor : Real.sin u ≤ v21RootSinUpper9 u := by
    simpa [v21RootSinUpper9] using v21_sin_upper9 hu0 hu1
  apply v26_ball_of_bounds
  · exact hlo.trans hlowTaylor
  · exact hhighTaylor.trans hhi

/-- The analogous cosine enclosure from the already kernel-checked Taylor
bounds. -/
lemma v26_cos_ball_of_taylor_bounds {u clo chi : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hlo : clo ≤ v21RootCosLower10 u)
    (hhi : v21RootCosUpper8 u ≤ chi) :
    v26Ball (Real.cos u) ((clo + chi) / 2) ((chi - clo) / 2) := by
  have hlowTaylor : v21RootCosLower10 u ≤ Real.cos u := by
    simpa [v21RootCosLower10] using v21_cos_lower10 hu0 hu1
  have hhighTaylor : Real.cos u ≤ v21RootCosUpper8 u := by
    simpa [v21RootCosUpper8] using v21_cos_upper8 hu0 hu1
  apply v26_ball_of_bounds
  · exact hlo.trans hlowTaylor
  · exact hhighTaylor.trans hhi

end HurtadoZeta23
