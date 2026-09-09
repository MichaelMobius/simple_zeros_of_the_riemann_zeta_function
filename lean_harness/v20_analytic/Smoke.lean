import HurtadoZeta23.V17KernelMonotonicity
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

example : v17KernelCertPoint = (89 / 100 : ℝ) := by
  rfl

example : (171389 / 1000000 : ℝ) < 1 := by
  norm_num

end HurtadoZeta23
