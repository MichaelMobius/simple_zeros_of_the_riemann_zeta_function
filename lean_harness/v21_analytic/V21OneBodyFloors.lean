import HurtadoZeta23.V21KernelB1Ramp
import HurtadoZeta23.V21HardCoreGeometry
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The exact coordinate one-body contribution appearing in the six-gap
functional. -/
def v21OneBody (j : Fin 6) (x : ℝ) : ℝ :=
  pressure j * x + (1 / 3 : ℝ) * limitingWeight x

/-- Rational one-body floors used by the analytic bootstrap. -/
def v21Lambda (j : Fin 6) : ℝ :=
  if j = (0 : Fin 6) ∨ j = (5 : Fin 6) then (285 / 1000000 : ℝ)
  else if j = (1 : Fin 6) ∨ j = (4 : Fin 6) then (393 / 1000000 : ℝ)
  else (374 / 1000000 : ℝ)

lemma v21_lambda_le_max (j : Fin 6) :
    v21Lambda j ≤ (393 / 1000000 : ℝ) := by
  fin_cases j <;> norm_num [v21Lambda]

lemma v21_lambda_values :
    v21Lambda (0 : Fin 6) = (285 / 1000000 : ℝ) ∧
    v21Lambda (1 : Fin 6) = (393 / 1000000 : ℝ) ∧
    v21Lambda (2 : Fin 6) = (374 / 1000000 : ℝ) ∧
    v21Lambda (3 : Fin 6) = (374 / 1000000 : ℝ) ∧
    v21Lambda (4 : Fin 6) = (393 / 1000000 : ℝ) ∧
    v21Lambda (5 : Fin 6) = (285 / 1000000 : ℝ) := by
  norm_num [v21Lambda]

/-- Public rational-center form of the strong first-band quadratic.  This
forgets the private convenience alias used in `V21KernelB1Ramp`. -/
lemma v21_one_third_weight_B1_quadratic_rat {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    (7 / 40 : ℝ) * (x - (211455 / 200000 : ℝ)) ^ 2 -
        (280053 / 64000000000000 : ℝ) ≤
      (1 / 3 : ℝ) * limitingWeight x := by
  have h := v21_one_third_weight_B1_quadratic hxlo hxhi
  change
    (7 / 40 : ℝ) * (x - v21RootMid 1) ^ 2 -
        (280053 / 64000000000000 : ℝ) ≤
      (1 / 3 : ℝ) * limitingWeight x at h
  simpa [v21RootMid, v21RootLeft, v21RootRight] using h

/-- On the first survivor band the strong kernel ramp gives the desired
position-dependent one-body floor. -/
lemma v21_one_body_floor_B1 (j : Fin 6) {x : ℝ}
    (hxlo : (19 / 20 : ℝ) ≤ x) (hxhi : x ≤ (6 / 5 : ℝ)) :
    v21Lambda j ≤ v21OneBody j x := by
  have hq := v21_one_third_weight_B1_quadratic_rat hxlo hxhi
  have hs0 :
      0 ≤ (x - (211455 / 200000 : ℝ) + (2714 / 3500000 : ℝ)) ^ 2 :=
    sq_nonneg _
  have hs1 :
      0 ≤ (x - (211455 / 200000 : ℝ) + (3733 / 3500000 : ℝ)) ^ 2 :=
    sq_nonneg _
  have hs2 :
      0 ≤ (x - (211455 / 200000 : ℝ) + (3553 / 3500000 : ℝ)) ^ 2 :=
    sq_nonneg _
  fin_cases j
  all_goals
    simp [v21OneBody, v21Lambda, pressure]
    nlinarith [hq, hs0, hs1, hs2]

/-- From the second survivor band onward pressure alone is already stronger
than the largest of the six selected floors. -/
lemma v21_one_body_floor_of_ge_179 (j : Fin 6) {x : ℝ}
    (hx : (179 / 100 : ℝ) ≤ x) :
    v21Lambda j ≤ v21OneBody j x := by
  have hx0 : 0 ≤ x := by nlinarith
  have hp := v21_pressure_min j
  have hmul :
      (2714 / 10000000 : ℝ) * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  have hbase :
      (393 / 1000000 : ℝ) ≤ (2714 / 10000000 : ℝ) * x := by
    nlinarith
  have hlam := v21_lambda_le_max j
  have hw := limitingWeight_nonneg x
  unfold v21OneBody
  nlinarith

/-- Every survivor band carries the exact floor vector
`(285,393,374,374,393,285) / 10^6`. -/
lemma v21_one_body_floor_of_band (j : Fin 6) {x : ℝ}
    (hband : v21GapBands x) :
    v21Lambda j ≤ v21OneBody j x := by
  rcases hband with h1 | h23
  · exact v21_one_body_floor_B1 j h1.1 h1.2
  · rcases h23 with h2 | h3
    · exact v21_one_body_floor_of_ge_179 j h2.1
    · exact v21_one_body_floor_of_ge_179 j (by linarith [h3.1])

lemma v21_lambda_total :
    v21Lambda (0 : Fin 6) + v21Lambda (1 : Fin 6) +
      v21Lambda (2 : Fin 6) + v21Lambda (3 : Fin 6) +
      v21Lambda (4 : Fin 6) + v21Lambda (5 : Fin 6) =
        (2104 / 1000000 : ℝ) := by
  norm_num [v21Lambda]

/-- The sum of the six exact one-body pieces is below the full functional;
all longer-block kernel terms are nonnegative. -/
lemma v21_one_body_sum_le_gapF
    (g0 g1 g2 g3 g4 g5 : ℝ) :
    v21OneBody (0 : Fin 6) g0 + v21OneBody (1 : Fin 6) g1 +
      v21OneBody (2 : Fin 6) g2 + v21OneBody (3 : Fin 6) g3 +
      v21OneBody (4 : Fin 6) g4 + v21OneBody (5 : Fin 6) g5 ≤
        v21GapF g0 g1 g2 g3 g4 g5 := by
  have h01 := limitingWeight_nonneg (g0 + g1)
  have h12 := limitingWeight_nonneg (g1 + g2)
  have h23 := limitingWeight_nonneg (g2 + g3)
  have h34 := limitingWeight_nonneg (g3 + g4)
  have h45 := limitingWeight_nonneg (g4 + g5)
  have h012 := limitingWeight_nonneg (g0 + g1 + g2)
  have h123 := limitingWeight_nonneg (g1 + g2 + g3)
  have h234 := limitingWeight_nonneg (g2 + g3 + g4)
  have h345 := limitingWeight_nonneg (g3 + g4 + g5)
  have h0123 := limitingWeight_nonneg (g0 + g1 + g2 + g3)
  have h1234 := limitingWeight_nonneg (g1 + g2 + g3 + g4)
  have h2345 := limitingWeight_nonneg (g2 + g3 + g4 + g5)
  have h01234 := limitingWeight_nonneg (g0 + g1 + g2 + g3 + g4)
  have h12345 := limitingWeight_nonneg (g1 + g2 + g3 + g4 + g5)
  have h012345 := limitingWeight_nonneg (g0 + g1 + g2 + g3 + g4 + g5)
  unfold v21OneBody v21GapF
  nlinarith

/-- A strict counterexample whose six coordinates have already survived the
one-dimensional exclusions forces the exact coordinate thresholds used by the
univariate basin bootstrap. -/
theorem v21_one_body_thresholds_of_bands_counterexample
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (hb0 : v21GapBands g0) (hb1 : v21GapBands g1)
    (hb2 : v21GapBands g2) (hb3 : v21GapBands g3)
    (hb4 : v21GapBands g4) (hb5 : v21GapBands g5)
    (hbad : v21GapF g0 g1 g2 g3 g4 g5 < delta) :
    v21OneBody (0 : Fin 6) g0 < (2081 / 1000000 : ℝ) ∧
    v21OneBody (1 : Fin 6) g1 < (2189 / 1000000 : ℝ) ∧
    v21OneBody (2 : Fin 6) g2 < (2170 / 1000000 : ℝ) ∧
    v21OneBody (3 : Fin 6) g3 < (2170 / 1000000 : ℝ) ∧
    v21OneBody (4 : Fin 6) g4 < (2189 / 1000000 : ℝ) ∧
    v21OneBody (5 : Fin 6) g5 < (2081 / 1000000 : ℝ) := by
  have hf0 := v21_one_body_floor_of_band (0 : Fin 6) hb0
  have hf1 := v21_one_body_floor_of_band (1 : Fin 6) hb1
  have hf2 := v21_one_body_floor_of_band (2 : Fin 6) hb2
  have hf3 := v21_one_body_floor_of_band (3 : Fin 6) hb3
  have hf4 := v21_one_body_floor_of_band (4 : Fin 6) hb4
  have hf5 := v21_one_body_floor_of_band (5 : Fin 6) hb5
  have hsum := v21_one_body_sum_le_gapF g0 g1 g2 g3 g4 g5
  norm_num [v21Lambda] at hf0 hf1 hf2 hf3 hf4 hf5
  norm_num [delta] at hbad
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end HurtadoZeta23