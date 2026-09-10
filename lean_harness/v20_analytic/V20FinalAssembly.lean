import HurtadoZeta23.V20KernelSignedAnalytic
import HurtadoZeta23.V17FinalAssembly

noncomputable section

namespace HurtadoZeta23

/-- The v17 signed-kernel frontier is now discharged internally by the
analytic Lean theorem at the exact certification point `89/100`. -/
theorem v20_kernel_signed_claim : V17KernelSignedCertPointClaim := by
  unfold V17KernelSignedCertPointClaim
  rw [v17KernelCertPoint]
  exact v20_kernel_signed_89_100

/-- v20 end-to-end global refinement.  The only explicit external certificate
input left at this wrapper is the archived seven-point finite inequality. -/
noncomputable def v20GlobalRefinement
    (hcertExt : ArchivedSevenPointClaim) : V17GlobalRefinement :=
  v17GlobalRefinement_of_certificates hcertExt v20_kernel_signed_claim

/-- Published epsilon form with the signed kernel enclosure removed from the
external trust boundary.  The numerical constant is exactly the v17 published
constant; v20 changes formal provenance, not the quantitative bound. -/
theorem v20_published_eps_form
    (hcertExt : ArchivedSevenPointClaim) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (v17PublishedConstant - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  exact v17_published_eps_form_of_certificates
    hcertExt v20_kernel_signed_claim

end HurtadoZeta23
