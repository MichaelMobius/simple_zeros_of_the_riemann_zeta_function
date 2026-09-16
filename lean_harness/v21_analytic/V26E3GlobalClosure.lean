import HurtadoZeta23.V26PackageD
import HurtadoZeta23.V26E3BootstrapClosureGenerated
import HurtadoZeta23.V21GapFunctional
import HurtadoZeta23.V20FinalAssembly

noncomputable section
namespace HurtadoZeta23

/-- Package D + full Package E3 finite closure.  Under the exact hard-core
geometric hypotheses used by Package D, the limiting six-gap functional cannot
fall strictly below `v26Delta`. -/
theorem v26_no_hardcore_counterexample_limitingWeight
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v26HardCorePoint < g0)
    (h1 : v26HardCorePoint < g1)
    (h2 : v26HardCorePoint < g2)
    (h3 : v26HardCorePoint < g3)
    (h4 : v26HardCorePoint < g4)
    (h5 : v26HardCorePoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ)) :
    v26Delta ≤ v26GapF limitingWeight g0 g1 g2 g3 g4 g5 := by
  by_contra h
  have hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta :=
    lt_of_not_ge h
  rcases v26_counterexample_mem_511_limitingWeight
      g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum hbad with
    ⟨w, hw511, hbox⟩
  exact v26_E3_close_511
    w hw511 g0 g1 g2 g3 g4 g5 hbox hbad

/-- Contradiction form of `v26_no_hardcore_counterexample_limitingWeight`. -/
theorem v26_E3_no_strict_hardcore_counterexample
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v26HardCorePoint < g0)
    (h1 : v26HardCorePoint < g1)
    (h2 : v26HardCorePoint < g2)
    (h3 : v26HardCorePoint < g3)
    (h4 : v26HardCorePoint < g4)
    (h5 : v26HardCorePoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ))
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) : False := by
  have hge := v26_no_hardcore_counterexample_limitingWeight
    g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum
  linarith

/-- The finite-certificate target is exactly the article's historical delta. -/
theorem v26_delta_eq_article_delta : v26Delta = delta := by
  norm_num [v26Delta, delta]

/-- The v26 six-gap functional is definitionally the same seven-point gap
functional used by the article, after specializing the abstract weight to
`limitingWeight`.  This theorem keeps the notation bridge explicit. -/
theorem v26_gapF_eq_v21_gapF
    (g0 g1 g2 g3 g4 g5 : ℝ) :
    v26GapF limitingWeight g0 g1 g2 g3 g4 g5 =
      v21GapF g0 g1 g2 g3 g4 g5 := by
  simp [v26GapF, v21GapF, v26Pressure, pressure]

/-- The completed v26 finite closure discharges the exact six-variable hard
core proposition previously left as the numerical heart of the article. -/
theorem v26_gap_hard_core_claim : V21GapHardCoreClaim := by
  intro g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum
  have hge := v26_no_hardcore_counterexample_limitingWeight
    g0 g1 g2 g3 g4 g5
    (by simpa [v26HardCorePoint, v17KernelCertPoint] using h0)
    (by simpa [v26HardCorePoint, v17KernelCertPoint] using h1)
    (by simpa [v26HardCorePoint, v17KernelCertPoint] using h2)
    (by simpa [v26HardCorePoint, v17KernelCertPoint] using h3)
    (by simpa [v26HardCorePoint, v17KernelCertPoint] using h4)
    (by simpa [v26HardCorePoint, v17KernelCertPoint] using h5)
    hsum
  rw [v26_delta_eq_article_delta] at hge
  rw [v26_gapF_eq_v21_gapF] at hge
  exact hge

/-- Fully internal replacement for the archived Arb/FLINT seven-point
certificate: the article's seven-point inequality now follows from the
analytic kernel theorem and the exact rational E3 finite closure. -/
theorem v26_article_seven_point_inequality : ArticleSevenPointInequality := by
  exact v21_article_of_gap_hard_core
    v20_kernel_signed_claim v26_gap_hard_core_claim

/-- Global refinement with no external seven-point certificate argument. -/
noncomputable def v26GlobalRefinement : V17GlobalRefinement :=
  v20GlobalRefinement v26_article_seven_point_inequality

/-- Published epsilon form with both historical numerical frontiers discharged
inside Lean: the signed kernel enclosure is analytic (v20), and the six-gap
certificate is the exact rational E3 closure (v26). -/
theorem v26_published_eps_form :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (v17PublishedConstant - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  exact v20_published_eps_form v26_article_seven_point_inequality

end HurtadoZeta23
