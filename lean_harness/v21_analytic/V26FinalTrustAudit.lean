import HurtadoZeta23.V26E3GlobalClosure

noncomputable section
namespace HurtadoZeta23

/-!
# v26 final trust audit

This module contains no new proof.  It asks Lean to report the axioms on which
the final internally closed seven-point theorem and published epsilon theorem
depend.  The corresponding CI job records the output in the GitHub Actions log.
-/

#check v26_article_seven_point_inequality
#check v26_published_eps_form

#print axioms v20_kernel_signed_claim
#print axioms v26_article_seven_point_inequality
#print axioms v26_published_eps_form

end HurtadoZeta23
