import HurtadoZeta23.V26OneBodyExclusionA
import HurtadoZeta23.V26OneBodyExclusionB
import HurtadoZeta23.V26OneBodyExclusionC
import HurtadoZeta23.V26OneBodyGlobalFloors
import HurtadoZeta23.V26BasinInterface
import Mathlib.Tactic

noncomputable section
namespace HurtadoZeta23

/-- A strict sub-threshold type-A one-body value on the hard core lies in a published basin. -/
theorem v26_localize_A_of_below {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hbelow : (1357 / 5000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x < (2081 / 1000000 : ℝ)) :
    ∃ i : Fin 7, v26InA i x := by
  have hw := v26_limitingWeight_nonneg x
  have hcap : x < (10405 / 1357 : ℝ) := by nlinarith
  by_cases hLA1 : (191 / 200 : ℝ) ≤ x
  · by_cases hUA1 : x ≤ (579 / 500 : ℝ)
    · refine ⟨(0 : Fin 7), ?_⟩
      norm_num [v26InA, v26ALo, v26AHi] at hLA1 hUA1 ⊢
      exact ⟨hLA1, hUA1⟩
    · have hafterA1 : (579 / 500 : ℝ) ≤ x := by linarith
      by_cases hLA2 : (224 / 125 : ℝ) ≤ x
      · by_cases hUA2 : x ≤ (1129 / 500 : ℝ)
        · refine ⟨(1 : Fin 7), ?_⟩
          norm_num [v26InA, v26ALo, v26AHi] at hLA2 hUA2 ⊢
          exact ⟨hLA2, hUA2⟩
        · have hafterA2 : (1129 / 500 : ℝ) ≤ x := by linarith
          by_cases hLA3 : (653 / 250 : ℝ) ≤ x
          · by_cases hUA3 : x ≤ (849 / 250 : ℝ)
            · refine ⟨(2 : Fin 7), ?_⟩
              norm_num [v26InA, v26ALo, v26AHi] at hLA3 hUA3 ⊢
              exact ⟨hLA3, hUA3⟩
            · have hafterA3 : (849 / 250 : ℝ) ≤ x := by linarith
              by_cases hLA4 : (1751 / 500 : ℝ) ≤ x
              · by_cases hUA4 : x ≤ (893 / 200 : ℝ)
                · refine ⟨(3 : Fin 7), ?_⟩
                  norm_num [v26InA, v26ALo, v26AHi] at hLA4 hUA4 ⊢
                  exact ⟨hLA4, hUA4⟩
                · have hafterA4 : (893 / 200 : ℝ) ≤ x := by linarith
                  by_cases hLA5 : (9 / 2 : ℝ) ≤ x
                  · by_cases hUA5 : x ≤ (2733 / 500 : ℝ)
                    · refine ⟨(4 : Fin 7), ?_⟩
                      norm_num [v26InA, v26ALo, v26AHi] at hLA5 hUA5 ⊢
                      exact ⟨hLA5, hUA5⟩
                    · have hafterA5 : (2733 / 500 : ℝ) ≤ x := by linarith
                      by_cases hLA6 : (11 / 2 : ℝ) ≤ x
                      · by_cases hUA6 : x ≤ (6413 / 1000 : ℝ)
                        · refine ⟨(5 : Fin 7), ?_⟩
                          norm_num [v26InA, v26ALo, v26AHi] at hLA6 hUA6 ⊢
                          exact ⟨hLA6, hUA6⟩
                        · have hafterA6 : (6413 / 1000 : ℝ) ≤ x := by linarith
                          by_cases hLA7 : (822 / 125 : ℝ) ≤ x
                          · by_cases hUA7 : x ≤ (727 / 100 : ℝ)
                            · refine ⟨(6 : Fin 7), ?_⟩
                              norm_num [v26InA, v26ALo, v26AHi] at hLA7 hUA7 ⊢
                              exact ⟨hLA7, hUA7⟩
                            · have hafterA7 : (727 / 100 : ℝ) ≤ x := by linarith
                              have hxcap : x ≤ (10405 / 1357 : ℝ) := by linarith
                              have hex := v26_excl_A_parent8 hx89 hafterA7 hxcap
                              exfalso
                              linarith
                          · have hxnext : x ≤ (822 / 125 : ℝ) := by linarith
                            have hex := v26_excl_A_parent7 hx89 hafterA6 hxnext
                            exfalso
                            linarith
                      · have hxnext : x ≤ (11 / 2 : ℝ) := by linarith
                        have hex := v26_excl_A_parent6 hx89 hafterA5 hxnext
                        exfalso
                        linarith
                  · have hxnext : x ≤ (9 / 2 : ℝ) := by linarith
                    have hex := v26_excl_A_parent5 hx89 hafterA4 hxnext
                    exfalso
                    linarith
              · have hxnext : x ≤ (1751 / 500 : ℝ) := by linarith
                have hex := v26_excl_A_parent4 hx89 hafterA3 hxnext
                exfalso
                linarith
          · have hxnext : x ≤ (653 / 250 : ℝ) := by linarith
            have hex := v26_excl_A_parent3 hx89 hafterA2 hxnext
            exfalso
            linarith
      · have hxnext : x ≤ (224 / 125 : ℝ) := by linarith
        have hex := v26_excl_A_parent2 hx89 hafterA1 hxnext
        exfalso
        linarith
  · have hxfirst : x ≤ (191 / 200 : ℝ) := by linarith
    have hex := v26_excl_A_parent1 hx89 (le_of_lt hx89) hxfirst
    exfalso
    linarith

/-- A strict sub-threshold type-B one-body value on the hard core lies in a published basin. -/
theorem v26_localize_B_of_below {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hbelow : (3733 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x < (2189 / 1000000 : ℝ)) :
    ∃ i : Fin 5, v26InB i x := by
  have hw := v26_limitingWeight_nonneg x
  have hcap : x < (21890 / 3733 : ℝ) := by nlinarith
  by_cases hLB1 : (191 / 200 : ℝ) ≤ x
  · by_cases hUB1 : x ≤ (579 / 500 : ℝ)
    · refine ⟨(0 : Fin 5), ?_⟩
      norm_num [v26InB, v26BLo, v26BHi] at hLB1 hUB1 ⊢
      exact ⟨hLB1, hUB1⟩
    · have hafterB1 : (579 / 500 : ℝ) ≤ x := by linarith
      by_cases hLB2 : (899 / 500 : ℝ) ≤ x
      · by_cases hUB2 : x ≤ (2249 / 1000 : ℝ)
        · refine ⟨(1 : Fin 5), ?_⟩
          norm_num [v26InB, v26BLo, v26BHi] at hLB2 hUB2 ⊢
          exact ⟨hLB2, hUB2⟩
        · have hafterB2 : (2249 / 1000 : ℝ) ≤ x := by linarith
          by_cases hLB3 : (2637 / 1000 : ℝ) ≤ x
          · by_cases hUB3 : x ≤ (1679 / 500 : ℝ)
            · refine ⟨(2 : Fin 5), ?_⟩
              norm_num [v26InB, v26BLo, v26BHi] at hLB3 hUB3 ⊢
              exact ⟨hLB3, hUB3⟩
            · have hafterB3 : (1679 / 500 : ℝ) ≤ x := by linarith
              by_cases hLB4 : (446 / 125 : ℝ) ≤ x
              · by_cases hUB4 : x ≤ (35 / 8 : ℝ)
                · refine ⟨(3 : Fin 5), ?_⟩
                  norm_num [v26InB, v26BLo, v26BHi] at hLB4 hUB4 ⊢
                  exact ⟨hLB4, hUB4⟩
                · have hafterB4 : (35 / 8 : ℝ) ≤ x := by linarith
                  by_cases hLB5 : (4611 / 1000 : ℝ) ≤ x
                  · by_cases hUB5 : x ≤ (1057 / 200 : ℝ)
                    · refine ⟨(4 : Fin 5), ?_⟩
                      norm_num [v26InB, v26BLo, v26BHi] at hLB5 hUB5 ⊢
                      exact ⟨hLB5, hUB5⟩
                    · have hafterB5 : (1057 / 200 : ℝ) ≤ x := by linarith
                      have hxcap : x ≤ (21890 / 3733 : ℝ) := by linarith
                      have hex := v26_excl_B_parent6 hx89 hafterB5 hxcap
                      exfalso
                      linarith
                  · have hxnext : x ≤ (4611 / 1000 : ℝ) := by linarith
                    have hex := v26_excl_B_parent5 hx89 hafterB4 hxnext
                    exfalso
                    linarith
              · have hxnext : x ≤ (446 / 125 : ℝ) := by linarith
                have hex := v26_excl_B_parent4 hx89 hafterB3 hxnext
                exfalso
                linarith
          · have hxnext : x ≤ (2637 / 1000 : ℝ) := by linarith
            have hex := v26_excl_B_parent3 hx89 hafterB2 hxnext
            exfalso
            linarith
      · have hxnext : x ≤ (899 / 500 : ℝ) := by linarith
        have hex := v26_excl_B_parent2 hx89 hafterB1 hxnext
        exfalso
        linarith
  · have hxfirst : x ≤ (191 / 200 : ℝ) := by linarith
    have hex := v26_excl_B_parent1 hx89 (le_of_lt hx89) hxfirst
    exfalso
    linarith

/-- A strict sub-threshold type-C one-body value on the hard core lies in a published basin. -/
theorem v26_localize_C_of_below {x : ℝ}
    (hx89 : (89 / 100 : ℝ) < x)
    (hbelow : (3553 / 10000000 : ℝ) * x + (1 / 3 : ℝ) * limitingWeight x < (217 / 100000 : ℝ)) :
    ∃ i : Fin 6, v26InC i x := by
  have hw := v26_limitingWeight_nonneg x
  have hcap : x < (21700 / 3553 : ℝ) := by nlinarith
  by_cases hLC1 : (191 / 200 : ℝ) ≤ x
  · by_cases hUC1 : x ≤ (579 / 500 : ℝ)
    · refine ⟨(0 : Fin 6), ?_⟩
      norm_num [v26InC, v26CLo, v26CHi] at hLC1 hUC1 ⊢
      exact ⟨hLC1, hUC1⟩
    · have hafterC1 : (579 / 500 : ℝ) ≤ x := by linarith
      by_cases hLC2 : (1797 / 1000 : ℝ) ≤ x
      · by_cases hUC2 : x ≤ (2251 / 1000 : ℝ)
        · refine ⟨(1 : Fin 6), ?_⟩
          norm_num [v26InC, v26CLo, v26CHi] at hLC2 hUC2 ⊢
          exact ⟨hLC2, hUC2⟩
        · have hafterC2 : (2251 / 1000 : ℝ) ≤ x := by linarith
          by_cases hLC3 : (2633 / 1000 : ℝ) ≤ x
          · by_cases hUC3 : x ≤ (673 / 200 : ℝ)
            · refine ⟨(2 : Fin 6), ?_⟩
              norm_num [v26InC, v26CLo, v26CHi] at hLC3 hUC3 ⊢
              exact ⟨hLC3, hUC3⟩
            · have hafterC3 : (673 / 200 : ℝ) ≤ x := by linarith
              by_cases hLC4 : (889 / 250 : ℝ) ≤ x
              · by_cases hUC4 : x ≤ (549 / 125 : ℝ)
                · refine ⟨(3 : Fin 6), ?_⟩
                  norm_num [v26InC, v26CLo, v26CHi] at hLC4 hUC4 ⊢
                  exact ⟨hLC4, hUC4⟩
                · have hafterC4 : (549 / 125 : ℝ) ≤ x := by linarith
                  by_cases hLC5 : (229 / 50 : ℝ) ≤ x
                  · by_cases hUC5 : x ≤ (2661 / 500 : ℝ)
                    · refine ⟨(4 : Fin 6), ?_⟩
                      norm_num [v26InC, v26CLo, v26CHi] at hLC5 hUC5 ⊢
                      exact ⟨hLC5, hUC5⟩
                    · have hafterC5 : (2661 / 500 : ℝ) ≤ x := by linarith
                      by_cases hLC6 : (5793 / 1000 : ℝ) ≤ x
                      · by_cases hUC6 : x ≤ (3039 / 500 : ℝ)
                        · refine ⟨(5 : Fin 6), ?_⟩
                          norm_num [v26InC, v26CLo, v26CHi] at hLC6 hUC6 ⊢
                          exact ⟨hLC6, hUC6⟩
                        · have hafterC6 : (3039 / 500 : ℝ) ≤ x := by linarith
                          have hxcap : x ≤ (21700 / 3553 : ℝ) := by linarith
                          have hex := v26_excl_C_parent7 hx89 hafterC6 hxcap
                          exfalso
                          linarith
                      · have hxnext : x ≤ (5793 / 1000 : ℝ) := by linarith
                        have hex := v26_excl_C_parent6 hx89 hafterC5 hxnext
                        exfalso
                        linarith
                  · have hxnext : x ≤ (229 / 50 : ℝ) := by linarith
                    have hex := v26_excl_C_parent5 hx89 hafterC4 hxnext
                    exfalso
                    linarith
              · have hxnext : x ≤ (889 / 250 : ℝ) := by linarith
                have hex := v26_excl_C_parent4 hx89 hafterC3 hxnext
                exfalso
                linarith
          · have hxnext : x ≤ (2633 / 1000 : ℝ) := by linarith
            have hex := v26_excl_C_parent3 hx89 hafterC2 hxnext
            exfalso
            linarith
      · have hxnext : x ≤ (1797 / 1000 : ℝ) := by linarith
        have hex := v26_excl_C_parent2 hx89 hafterC1 hxnext
        exfalso
        linarith
  · have hxfirst : x ≤ (191 / 200 : ℝ) := by linarith
    have hex := v26_excl_C_parent1 hx89 (le_of_lt hx89) hxfirst
    exfalso
    linarith

/-- The global one-body floors force the published positional thresholds
for every strict six-gap counterexample on the hard core. -/
theorem v26_onebody_thresholds_of_counterexample
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : (89 / 100 : ℝ) < g0)
    (h1 : (89 / 100 : ℝ) < g1)
    (h2 : (89 / 100 : ℝ) < g2)
    (h3 : (89 / 100 : ℝ) < g3)
    (h4 : (89 / 100 : ℝ) < g4)
    (h5 : (89 / 100 : ℝ) < g5)
    (hbad : v26GapF limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta) :
    ((1357 / 5000000 : ℝ) * g0 + (1 / 3 : ℝ) * limitingWeight g0 < (2081 / 1000000 : ℝ)) ∧
    ((3733 / 10000000 : ℝ) * g1 + (1 / 3 : ℝ) * limitingWeight g1 < (2189 / 1000000 : ℝ)) ∧
    ((3553 / 10000000 : ℝ) * g2 + (1 / 3 : ℝ) * limitingWeight g2 < (217 / 100000 : ℝ)) ∧
    ((3553 / 10000000 : ℝ) * g3 + (1 / 3 : ℝ) * limitingWeight g3 < (217 / 100000 : ℝ)) ∧
    ((3733 / 10000000 : ℝ) * g4 + (1 / 3 : ℝ) * limitingWeight g4 < (2189 / 1000000 : ℝ)) ∧
    ((1357 / 5000000 : ℝ) * g5 + (1 / 3 : ℝ) * limitingWeight g5 < (2081 / 1000000 : ℝ)) := by
  have hf0 := v26_lambda_A h0
  have hf1 := v26_lambda_B h1
  have hf2 := v26_lambda_C h2
  have hf3 := v26_lambda_C h3
  have hf4 := v26_lambda_B h4
  have hf5 := v26_lambda_A h5
  have hsumle := v26_oneBodySum_le_gapF limitingWeight v26_limitingWeight_nonneg g0 g1 g2 g3 g4 g5
  have hsumlt : v26OneBodySum limitingWeight g0 g1 g2 g3 g4 g5 < v26Delta :=
    lt_of_le_of_lt hsumle hbad
  simp [v26OneBodySum, v26Pressure] at hsumlt
  norm_num [v26Delta] at hsumlt
  constructor
  · nlinarith [hf1, hf2, hf3, hf4, hf5]
  constructor
  · nlinarith [hf0, hf2, hf3, hf4, hf5]
  constructor
  · nlinarith [hf0, hf1, hf3, hf4, hf5]
  constructor
  · nlinarith [hf0, hf1, hf2, hf4, hf5]
  constructor
  · nlinarith [hf0, hf1, hf2, hf3, hf5]
  · nlinarith [hf0, hf1, hf2, hf3, hf4]

/-- Package D localization half of the basin interface. -/
theorem v26_basin_localization : V26BasinLocalizationClaim limitingWeight := by
  intro g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 _hsum hbad
  rcases v26_onebody_thresholds_of_counterexample g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hbad with
    ⟨ht0, ht1, ht2, ht3, ht4, ht5⟩
  rcases v26_localize_A_of_below h0 ht0 with ⟨a, ha⟩
  rcases v26_localize_B_of_below h1 ht1 with ⟨b, hb⟩
  rcases v26_localize_C_of_below h2 ht2 with ⟨c, hc⟩
  rcases v26_localize_C_of_below h3 ht3 with ⟨d, hd⟩
  rcases v26_localize_B_of_below h4 ht4 with ⟨e, he⟩
  rcases v26_localize_A_of_below h5 ht5 with ⟨f, hf⟩
  exact ⟨(a, b, c, d, e, f), ha, hb, hc, hd, he, hf⟩

end HurtadoZeta23
