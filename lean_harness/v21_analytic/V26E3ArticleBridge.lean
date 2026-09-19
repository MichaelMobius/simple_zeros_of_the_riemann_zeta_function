import HurtadoZeta23.V26WordBridge
import HurtadoZeta23.V26BasinInterface
import HurtadoZeta23.V21GapFunctional

noncomputable section
namespace HurtadoZeta23

/-- The v26 finite-certificate target is exactly the article's historical
seven-point threshold. -/
theorem v26_delta_eq_article_delta : v26Delta = delta := by
  norm_num [v26Delta, delta]

/-- The v26 hard-core cutoff is exactly the signed-kernel certification point. -/
theorem v26_hardCorePoint_eq_v17KernelCertPoint :
    v26HardCorePoint = v17KernelCertPoint := by
  norm_num [v26HardCorePoint, v17KernelCertPoint]

/-- The v26 six-gap functional is exactly the article's seven-point gap
functional after specializing the abstract weight to `limitingWeight`. -/
theorem v26_gapF_eq_v21_gapF
    (g0 g1 g2 g3 g4 g5 : ℝ) :
    v26GapF limitingWeight g0 g1 g2 g3 g4 g5 =
      v21GapF g0 g1 g2 g3 g4 g5 := by
  simp [v26GapF, v21GapF, v26Pressure, pressure]

end HurtadoZeta23
