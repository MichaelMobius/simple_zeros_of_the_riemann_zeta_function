import HurtadoZeta23.V26PackageD
import HurtadoZeta23.V26R0DispatchGenerated

noncomputable section
namespace HurtadoZeta23

/-- End-to-end Package-D + Package-E3/R0 consequence.  Every strict hard-core
counterexample first localizes to one of the 511 Package-D basin words and is
then reduced by the exact R0 rational bootstrap to the published 231-code
Round1 set together with that word's exact contracted 21-block box. -/
theorem v26_counterexample_mem_231_limitingWeight
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v26HardCorePoint < g0)
    (h1 : v26HardCorePoint < g1)
    (h2 : v26HardCorePoint < g2)
    (h3 : v26HardCorePoint < g3)
    (h4 : v26HardCorePoint < g4)
    (h5 : v26HardCorePoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ))
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    ∃ w : V26BasinWord,
      v26InRound1 w ∧
      v26E3R0ContractedBox w g0 g1 g2 g3 g4 g5 := by
  rcases v26_counterexample_mem_511_limitingWeight
      g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum hbad with
    ⟨w, hw511, hbox⟩
  have hr0 := v26_E3_R0_reduce_511_to_231
    w hw511 g0 g1 g2 g3 g4 g5 hbox hbad
  exact ⟨w, hr0.1, hr0.2⟩

end HurtadoZeta23
