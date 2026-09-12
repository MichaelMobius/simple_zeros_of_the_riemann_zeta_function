import HurtadoZeta23.V21KernelCentralEndpointBounds
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

macro "b2_lower_endpoint" : tactic =>
  `(tactic|
    first
    | norm_num [v17KernelCertPoint, v21RootPiU, v21RootDenCap,
        v21RootCL, v21RootPiL]
    | (norm_num [v17KernelCertPoint, v21RootPiU, v21RootDenCap,
        v21RootCL, v21RootPiL] <;> positivity))

/-- Common left endpoint of the second coarse survivor band, viewed in the
central strip of lobe 1. -/
theorem v21_signed1_at_1790_lower :
    (7 / 100 : ℝ) ≤ v21SignedKernel 1 (179 / 100 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (29 / 100 : ℝ))
  all_goals b2_lower_endpoint

/-- Type-A lower edge of the second refined basin. -/
theorem v21_signed1_at_1792_lower :
    (695 / 10000 : ℝ) ≤ v21SignedKernel 1 (1792 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (292 / 1000 : ℝ))
  all_goals b2_lower_endpoint

/-- Type-B lower edge of the second refined basin.  This is the tightest of
the three lower-edge certificates. -/
theorem v21_signed1_at_1798_lower :
    (676 / 10000 : ℝ) ≤ v21SignedKernel 1 (1798 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (298 / 1000 : ℝ))
  all_goals b2_lower_endpoint

/-- Type-C lower edge of the second refined basin. -/
theorem v21_signed1_at_1797_lower :
    (679 / 10000 : ℝ) ≤ v21SignedKernel 1 (1797 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (297 / 1000 : ℝ))
  all_goals b2_lower_endpoint

end HurtadoZeta23
