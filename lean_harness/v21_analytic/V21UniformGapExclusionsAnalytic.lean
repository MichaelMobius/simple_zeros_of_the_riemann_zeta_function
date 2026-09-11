import HurtadoZeta23.V21HardCoreGeometry
import HurtadoZeta23.V21FirstGapExclusion
import HurtadoZeta23.V21KernelIntervalCurvature
import HurtadoZeta23.V21KernelHigherEndpointBounds
import HurtadoZeta23.V21KernelThirdLobeEndpoints
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

lemma v21_kernelX_eq_limitingk_of_cert_lt {x : ℝ}
    (hx : v17KernelCertPoint < x) :
    v21KernelX x = limitingk x := by
  unfold v21KernelX
  exact (v21_limitingk_eq_kernelB (v21_A_lt_B_of_cert_lt hx)).symm

/-- The second excluded interval is ruled out by concavity of the signed
second lobe and its two endpoint certificates. -/
theorem v21_second_gap_exclusion :
    ∀ x : ℝ, (6 / 5 : ℝ) < x → x < (179 / 100 : ℝ) →
      delta ≤ v21MinOneBody x := by
  intro x hx1 hx2
  let q : ℝ := 521 / 5000
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this

  have hmin :=
    v21_negKernelX_concave_second_band.min_le_of_mem_Icc
      (show (6 / 5 : ℝ) ∈ Icc (6 / 5 : ℝ) (179 / 100 : ℝ) by norm_num)
      (show (179 / 100 : ℝ) ∈ Icc (6 / 5 : ℝ) (179 / 100 : ℝ) by norm_num)
      (show x ∈ Icc (6 / 5 : ℝ) (179 / 100 : ℝ) from
        ⟨le_of_lt hx1, le_of_lt hx2⟩)
  have hmin' :
      min (-v21KernelX (6 / 5 : ℝ)) (-v21KernelX (179 / 100 : ℝ)) ≤
        -v21KernelX x := by
    simpa using hmin

  have h120cert : v17KernelCertPoint < (6 / 5 : ℝ) := by
    norm_num [v17KernelCertPoint]
  have h179cert : v17KernelCertPoint < (179 / 100 : ℝ) := by
    norm_num [v17KernelCertPoint]
  have h120 : q ≤ -v21KernelX (6 / 5 : ℝ) := by
    dsimp [q]
    rw [v21_kernelX_eq_limitingk_of_cert_lt h120cert]
    exact le_of_lt v21_negk_at_120_lower
  have h179 : q ≤ -v21KernelX (179 / 100 : ℝ) := by
    dsimp [q]
    rw [v21_kernelX_eq_limitingk_of_cert_lt h179cert]
    exact le_of_lt v21_negk_at_179_lower
  have hqx : q ≤ -v21KernelX x :=
    (le_min h120 h179).trans hmin'
  have hk : q ≤ -limitingk x := by
    rw [← v21_kernelX_eq_limitingk_of_cert_lt hxcert]
    exact hqx
  have hw : q ^ 2 ≤ limitingWeight x :=
    v21_weight_lower_of_negk_lower (by norm_num [q]) hk

  unfold v21MinOneBody
  change (39 / 10000 : ℝ) ≤
    (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x
  dsimp [q] at hw
  nlinarith

/-- The third excluded interval is ruled out by concavity of the third lobe.
The split at `2.55` keeps the one-body pressure margin uniformly positive. -/
theorem v21_third_gap_exclusion :
    ∀ x : ℝ, (237 / 100 : ℝ) < x → x < (261 / 100 : ℝ) →
      delta ≤ v21MinOneBody x := by
  intro x hx1 hx2
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  by_cases hx255 : x ≤ (51 / 20 : ℝ)
  · let q : ℝ := 993 / 10000
    have hmin :=
      v21_kernelX_concave_third_band.min_le_of_mem_Icc
        (show (237 / 100 : ℝ) ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) by norm_num)
        (show (51 / 20 : ℝ) ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) by norm_num)
        (show x ∈ Icc (237 / 100 : ℝ) (51 / 20 : ℝ) from
          ⟨le_of_lt hx1, hx255⟩)
    have h237cert : v17KernelCertPoint < (237 / 100 : ℝ) := by
      norm_num [v17KernelCertPoint]
    have h255cert : v17KernelCertPoint < (51 / 20 : ℝ) := by
      norm_num [v17KernelCertPoint]
    have h237 : q ≤ v21KernelX (237 / 100 : ℝ) := by
      dsimp [q]
      rw [v21_kernelX_eq_limitingk_of_cert_lt h237cert]
      exact le_of_lt v21_k_at_237_lower
    have h255 : q ≤ v21KernelX (51 / 20 : ℝ) := by
      dsimp [q]
      rw [v21_kernelX_eq_limitingk_of_cert_lt h255cert]
      exact le_of_lt v21_k_at_255_lower
    have hqx : q ≤ v21KernelX x :=
      (le_min h237 h255).trans hmin
    have hk : q ≤ limitingk x := by
      rw [← v21_kernelX_eq_limitingk_of_cert_lt hxcert]
      exact hqx
    have hw : q ^ 2 ≤ limitingWeight x :=
      v21_weight_lower_of_k_lower (by norm_num [q]) hk
    unfold v21MinOneBody
    change (39 / 10000 : ℝ) ≤
      (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x
    dsimp [q] at hw
    nlinarith
  · let q : ℝ := 491 / 5000
    have hx255' : (51 / 20 : ℝ) ≤ x := le_of_lt (lt_of_not_ge hx255)
    have hmin :=
      v21_kernelX_concave_third_band.min_le_of_mem_Icc
        (show (51 / 20 : ℝ) ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) by norm_num)
        (show (261 / 100 : ℝ) ∈ Icc (237 / 100 : ℝ) (261 / 100 : ℝ) by norm_num)
        (show x ∈ Icc (51 / 20 : ℝ) (261 / 100 : ℝ) from
          ⟨hx255', le_of_lt hx2⟩)
    have h255cert : v17KernelCertPoint < (51 / 20 : ℝ) := by
      norm_num [v17KernelCertPoint]
    have h261cert : v17KernelCertPoint < (261 / 100 : ℝ) := by
      norm_num [v17KernelCertPoint]
    have h255 : q ≤ v21KernelX (51 / 20 : ℝ) := by
      dsimp [q]
      rw [v21_kernelX_eq_limitingk_of_cert_lt h255cert]
      have hstrong := le_of_lt v21_k_at_255_lower
      norm_num at hstrong ⊢
      linarith
    have h261 : q ≤ v21KernelX (261 / 100 : ℝ) := by
      dsimp [q]
      rw [v21_kernelX_eq_limitingk_of_cert_lt h261cert]
      exact le_of_lt v21_k_at_261_lower
    have hqx : q ≤ v21KernelX x :=
      (le_min h255 h261).trans hmin
    have hk : q ≤ limitingk x := by
      rw [← v21_kernelX_eq_limitingk_of_cert_lt hxcert]
      exact hqx
    have hw : q ^ 2 ≤ limitingWeight x :=
      v21_weight_lower_of_k_lower (by norm_num [q]) hk
    unfold v21MinOneBody
    change (39 / 10000 : ℝ) ≤
      (2714 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x
    dsimp [q] at hw
    nlinarith

/-- Fully analytic proof of the three uniform one-dimensional exclusions. -/
theorem v21_uniform_gap_exclusions_analytic : V21UniformGapExclusionClaim := by
  exact ⟨v21_first_gap_exclusion, v21_second_gap_exclusion, v21_third_gap_exclusion⟩

end HurtadoZeta23
