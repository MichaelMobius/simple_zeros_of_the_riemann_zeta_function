import HurtadoZeta23.V26OneBodyLocalization
import HurtadoZeta23.V26OneBodyFloors
import HurtadoZeta23.V26BootstrapStageLists
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- Package D closes both analytic obligations exposed by `V26BasinInterface`
for the article's exact limiting kernel weight. -/
theorem v26_package_D :
    V26BasinLocalizationClaim limitingWeight ∧
    V26BasinMicroFloorClaim limitingWeight := by
  exact ⟨v26_basin_localization, v26_basin_micro_floors⟩

/-- End-to-end Package D consequence: every strict hard-core counterexample
lands in one of the exact 511 one-body survivor boxes. -/
theorem v26_counterexample_mem_511_limitingWeight
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v26HardCorePoint < g0)
    (h1 : v26HardCorePoint < g1)
    (h2 : v26HardCorePoint < g2)
    (h3 : v26HardCorePoint < g3)
    (h4 : v26HardCorePoint < g4)
    (h5 : v26HardCorePoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ))
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    ∃ w : V26BasinWord, w ∈ v26SurvivorWords ∧
      v26InWordBox w g0 g1 g2 g3 g4 g5 := by
  exact v26_counterexample_mem_511
    limitingWeight v26_limitingWeight_nonneg
    v26_basin_localization v26_basin_micro_floors
    g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum hbad

end HurtadoZeta23
