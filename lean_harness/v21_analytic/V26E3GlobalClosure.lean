import HurtadoZeta23.V26PackageD
import HurtadoZeta23.V26E3BootstrapClosureGenerated

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

end HurtadoZeta23
