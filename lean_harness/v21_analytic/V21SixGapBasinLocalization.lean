import HurtadoZeta23.V21OneBodyLocalization
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Once all six coordinates have survived the coarse band filter, any strict
counterexample is forced into the exact refined basin pattern A-B-C-C-B-A.
This is the formal entry point for the finite word bootstrap. -/
theorem v21_six_gap_basin_localization
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hb0 : v21GapBands g0) (hb1 : v21GapBands g1)
    (hb2 : v21GapBands g2) (hb3 : v21GapBands g3)
    (hb4 : v21GapBands g4) (hb5 : v21GapBands g5)
    (hbad : v21GapF g0 g1 g2 g3 g4 g5 < delta) :
    v21TypeABasins g0 ∧
    v21TypeBBasins g1 ∧
    v21TypeCBasins g2 ∧
    v21TypeCBasins g3 ∧
    v21TypeBBasins g4 ∧
    v21TypeABasins g5 := by
  rcases v21_one_body_thresholds_of_bands_counterexample
      g0 g1 g2 g3 g4 g5 hb0 hb1 hb2 hb3 hb4 hb5 hbad with
    ⟨ht0, ht1, ht2, ht3, ht4, ht5⟩
  have hpA0 : (2714 / 10000000 : ℝ) ≤ pressure (0 : Fin 6) := by
    norm_num [pressure]
  have hpB1 : (3733 / 10000000 : ℝ) ≤ pressure (1 : Fin 6) := by
    norm_num [pressure]
  have hpC2 : (3553 / 10000000 : ℝ) ≤ pressure (2 : Fin 6) := by
    norm_num [pressure]
  have hpC3 : (3553 / 10000000 : ℝ) ≤ pressure (3 : Fin 6) := by
    norm_num [pressure]
  have hpB4 : (3733 / 10000000 : ℝ) ≤ pressure (4 : Fin 6) := by
    norm_num [pressure]
  have hpA5 : (2714 / 10000000 : ℝ) ≤ pressure (5 : Fin 6) := by
    norm_num [pressure]
  exact ⟨
    v21_oneBody_localize_A hpA0 hb0 ht0,
    v21_oneBody_localize_B hpB1 hb1 ht1,
    v21_oneBody_localize_C hpC2 hb2 ht2,
    v21_oneBody_localize_C hpC3 hb3 ht3,
    v21_oneBody_localize_B hpB4 hb4 ht4,
    v21_oneBody_localize_A hpA5 hb5 ht5⟩

end HurtadoZeta23
