import HurtadoZeta23.ExternalCertificateFrontier
import HurtadoZeta23.V17KernelMonotonicity
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace HurtadoZeta23

/-- The literal seven-point functional, expanded into its 6 pressure terms and
21 kernel weights.  This is only a readable normal form for `localFp`; no new
mathematical assumption is introduced. -/
def v21ExplicitF (y : ℕ → ℝ) (s : ℕ) : ℝ :=
  pressure 0 * (y (s+1) - y s) +
  pressure 1 * (y (s+2) - y (s+1)) +
  pressure 2 * (y (s+3) - y (s+2)) +
  pressure 3 * (y (s+4) - y (s+3)) +
  pressure 4 * (y (s+5) - y (s+4)) +
  pressure 5 * (y (s+6) - y (s+5)) +
  (1/3 : ℝ) * (
    limitingWeight (y (s+1) - y s) +
    limitingWeight (y (s+2) - y (s+1)) +
    limitingWeight (y (s+3) - y (s+2)) +
    limitingWeight (y (s+4) - y (s+3)) +
    limitingWeight (y (s+5) - y (s+4)) +
    limitingWeight (y (s+6) - y (s+5))) +
  (2/5 : ℝ) * (
    limitingWeight (y (s+2) - y s) +
    limitingWeight (y (s+3) - y (s+1)) +
    limitingWeight (y (s+4) - y (s+2)) +
    limitingWeight (y (s+5) - y (s+3)) +
    limitingWeight (y (s+6) - y (s+4))) +
  (1/2 : ℝ) * (
    limitingWeight (y (s+3) - y s) +
    limitingWeight (y (s+4) - y (s+1)) +
    limitingWeight (y (s+5) - y (s+2)) +
    limitingWeight (y (s+6) - y (s+3))) +
  (2/3 : ℝ) * (
    limitingWeight (y (s+4) - y s) +
    limitingWeight (y (s+5) - y (s+1)) +
    limitingWeight (y (s+6) - y (s+2))) +
  limitingWeight (y (s+5) - y s) +
  limitingWeight (y (s+6) - y (s+1)) +
  2 * limitingWeight (y (s+6) - y s)

/-- The first and last three historical pressure coefficients each carry
exactly half of the total pressure mass. -/
lemma v21_pressure_half_masses :
    pressure 0 + pressure 1 + pressure 2 = (1/1000 : ℝ) ∧
    pressure 3 + pressure 4 + pressure 5 = (1/1000 : ℝ) := by
  constructor <;> simp [pressure] <;> norm_num

/-- Every historical pressure coefficient is at least the endpoint value
`2714 / 10^7`. -/
lemma v21_pressure_min (j : Fin 6) :
    (2714 / 10000000 : ℝ) ≤ pressure j := by
  fin_cases j <;> norm_num [pressure]

/-- The pressure cutoff used by the historical Arb verifier has the exact
positive margin `9 / 500000000` above `delta`. -/
lemma v21_pressure_cutoff_margin :
    (2714 / 10000000 : ℝ) * (1437 / 100 : ℝ) - delta
      = (9 / 500000000 : ℝ) := by
  norm_num [delta]

/-- Replacing every position-dependent pressure coefficient by its minimum
can only decrease the pressure on six nonnegative gaps. -/
lemma v21_pressure_floor_six
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) (h2 : 0 ≤ g2)
    (h3 : 0 ≤ g3) (h4 : 0 ≤ g4) (h5 : 0 ≤ g5) :
    (2714 / 10000000 : ℝ) * (g0 + g1 + g2 + g3 + g4 + g5) ≤
      pressure 0 * g0 + pressure 1 * g1 + pressure 2 * g2 +
      pressure 3 * g3 + pressure 4 * g4 + pressure 5 * g5 := by
  simp [pressure]
  nlinarith

/-- Hence a total six-gap span of at least `14.37` is already settled by the
linear pressure term alone.  The genuinely analytic problem is compact. -/
lemma v21_pressure_tail_six
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) (h2 : 0 ≤ g2)
    (h3 : 0 ≤ g3) (h4 : 0 ≤ g4) (h5 : 0 ≤ g5)
    (hspan : (1437 / 100 : ℝ) ≤ g0 + g1 + g2 + g3 + g4 + g5) :
    delta <
      pressure 0 * g0 + pressure 1 * g1 + pressure 2 * g2 +
      pressure 3 * g3 + pressure 4 * g4 + pressure 5 * g5 := by
  have hfloor := v21_pressure_floor_six g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5
  have hmargin := v21_pressure_cutoff_margin
  nlinarith

/-- The kernel part of the local seven-point functional is nonnegative. -/
lemma v21_localPairEnergy_nonneg (y : ℕ → ℝ) (s : ℕ) :
    0 ≤ localPairEnergy (limitingWeightOnPoints y) s := by
  unfold localPairEnergy
  apply Finset.sum_nonneg
  intro r0 hr0
  have hr0lt : r0 < 6 := Finset.mem_range.mp hr0
  have hdenNat : 0 < 6 - r0 := Nat.sub_pos_of_lt hr0lt
  have hden : 0 < ((6 - r0 : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hinner :
      0 ≤ ∑ i ∈ Finset.range (6 - r0),
        limitingWeightOnPoints y (s + i) (s + i + r0 + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    exact limitingWeightOnPoints_nonneg y (s + i) (s + i + r0 + 1)
  exact mul_nonneg (div_nonneg (by norm_num) hden.le) hinner

/-- Nonnegative gaps make the whole pressure contribution nonnegative. -/
lemma v21_localPressure_nonneg
    (y : ℕ → ℝ) (s : ℕ)
    (hgap : ∀ j : Fin 6, 0 ≤ windowGap y s j) :
    0 ≤ localPressure y s := by
  unfold localPressure
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (pressure_nonneg j) (hgap j)

/-- Every adjacent weight appears in `localPairEnergy` with coefficient `1/3`.
All other pair contributions are nonnegative, so this single contribution is
a rigorous lower bound for the pair energy. -/
lemma v21_adjacent_weight_le_localPairEnergy
    (y : ℕ → ℝ) (s : ℕ) (j : Fin 6) :
    (1 / 3 : ℝ) *
        limitingWeightOnPoints y (s + j.1) (s + j.1 + 1) ≤
      localPairEnergy (limitingWeightOnPoints y) s := by
  have hinner :
      limitingWeightOnPoints y (s + j.1) (s + j.1 + 1) ≤
        ∑ i ∈ Finset.range 6,
          limitingWeightOnPoints y (s + i) (s + i + 1) := by
    exact Finset.single_le_sum
      (fun i hi => limitingWeightOnPoints_nonneg y (s + i) (s + i + 1))
      (Finset.mem_range.mpr j.2)
  let outerTerm : ℕ → ℝ := fun r0 =>
    (2 / ((6 - r0 : ℕ) : ℝ)) *
      (∑ i ∈ Finset.range (6 - r0),
        limitingWeightOnPoints y (s + i) (s + i + r0 + 1))
  have houterNonneg :
      ∀ r0 ∈ Finset.range 6, 0 ≤ outerTerm r0 := by
    intro r0 hr0
    have hr0lt : r0 < 6 := Finset.mem_range.mp hr0
    have hdenNat : 0 < 6 - r0 := Nat.sub_pos_of_lt hr0lt
    have hden : 0 < ((6 - r0 : ℕ) : ℝ) := by
      exact_mod_cast hdenNat
    have hsum :
        0 ≤ ∑ i ∈ Finset.range (6 - r0),
          limitingWeightOnPoints y (s + i) (s + i + r0 + 1) := by
      apply Finset.sum_nonneg
      intro i hi
      exact limitingWeightOnPoints_nonneg y (s + i) (s + i + r0 + 1)
    exact mul_nonneg (div_nonneg (by norm_num) hden.le) hsum
  have houterRaw :
      outerTerm 0 ≤ ∑ r0 ∈ Finset.range 6, outerTerm r0 := by
    exact Finset.single_le_sum houterNonneg (by simp)
  have houter :
      (1 / 3 : ℝ) *
          (∑ i ∈ Finset.range 6,
            limitingWeightOnPoints y (s + i) (s + i + 1)) ≤
        localPairEnergy (limitingWeightOnPoints y) s := by
    simpa [outerTerm, localPairEnergy] using houterRaw
  have hscaled :=
    mul_le_mul_of_nonneg_left hinner (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  exact hscaled.trans houter

/-- The full local functional dominates its linear pressure part. -/
lemma v21_localPressure_le_localFp (y : ℕ → ℝ) (s : ℕ) :
    localPressure y s ≤ localFp (limitingWeightOnPoints y) y s := by
  rw [localFp_eq]
  linarith [v21_localPairEnergy_nonneg y s]

/-- Literal six-term expansion of the local pressure. -/
lemma v21_localPressure_eq_explicit (y : ℕ → ℝ) (s : ℕ) :
    localPressure y s =
      pressure 0 * (y (s+1) - y s) +
      pressure 1 * (y (s+2) - y (s+1)) +
      pressure 2 * (y (s+3) - y (s+2)) +
      pressure 3 * (y (s+4) - y (s+3)) +
      pressure 4 * (y (s+5) - y (s+4)) +
      pressure 5 * (y (s+6) - y (s+5)) := by
  simp only [localPressure, windowGap]
  norm_num [Fin.sum_univ_succ]
  simp [pressure]
  ring

/-- Direct compact reduction for the article target: any admissible window
whose total span is at least `14.37` already satisfies the desired bound.
Thus the remaining six-gap problem may be restricted to total span `< 14.37`. -/
theorem v21_localFp_of_large_span
    (y : ℕ → ℝ) (s : ℕ)
    (hgap : ∀ j : Fin 6, 0 ≤ windowGap y s j)
    (hspan : (1437 / 100 : ℝ) ≤ y (s+6) - y s) :
    delta ≤ localFp (limitingWeightOnPoints y) y s := by
  have h0 : 0 ≤ y (s+1) - y s := by
    simpa [windowGap] using hgap (0 : Fin 6)
  have h1 : 0 ≤ y (s+2) - y (s+1) := by
    simpa [windowGap] using hgap (1 : Fin 6)
  have h2 : 0 ≤ y (s+3) - y (s+2) := by
    simpa [windowGap] using hgap (2 : Fin 6)
  have h3 : 0 ≤ y (s+4) - y (s+3) := by
    simpa [windowGap] using hgap (3 : Fin 6)
  have h4 : 0 ≤ y (s+5) - y (s+4) := by
    simpa [windowGap] using hgap (4 : Fin 6)
  have h5 : 0 ≤ y (s+6) - y (s+5) := by
    simpa [windowGap] using hgap (5 : Fin 6)
  have hsum :
      (1437 / 100 : ℝ) ≤
        (y (s+1) - y s) + (y (s+2) - y (s+1)) +
        (y (s+3) - y (s+2)) + (y (s+4) - y (s+3)) +
        (y (s+5) - y (s+4)) + (y (s+6) - y (s+5)) := by
    linarith
  have htail :=
    v21_pressure_tail_six
      (y (s+1) - y s) (y (s+2) - y (s+1))
      (y (s+3) - y (s+2)) (y (s+4) - y (s+3))
      (y (s+5) - y (s+4)) (y (s+6) - y (s+5))
      h0 h1 h2 h3 h4 h5 hsum
  have hpressure := v21_localPressure_le_localFp y s
  rw [v21_localPressure_eq_explicit] at hpressure
  exact (le_of_lt htail).trans hpressure

/-- If one gap is at most the internally certified point `0.89`, its adjacent
kernel term alone already exceeds `delta`.  This theorem is parameterized by
the signed point statement; v20 proves that statement analytically in Lean. -/
theorem v21_localFp_of_small_gap
    (hsigned : V17KernelSignedCertPointClaim)
    (y : ℕ → ℝ) (s : ℕ)
    (hgap : ∀ j : Fin 6, 0 ≤ windowGap y s j)
    (j : Fin 6)
    (hsmall : windowGap y s j ≤ v17KernelCertPoint) :
    delta ≤ localFp (limitingWeightOnPoints y) y s := by
  have hmono :=
    v17_weight_cert_le_below_of_signed hsigned (hgap j) hsmall
  have hcert := v17_weight_cert_of_signed hsigned
  unfold V17KernelAtCertPointClaim at hcert
  have hweight :
      (2937 / 100000 : ℝ) < limitingWeight (windowGap y s j) :=
    hcert.trans_le hmono
  have hpoint :
      (2937 / 100000 : ℝ) <
        limitingWeightOnPoints y (s + j.1) (s + j.1 + 1) := by
    simpa [limitingWeightOnPoints, windowGap, Nat.add_assoc] using hweight
  have hterm :
      delta < (1 / 3 : ℝ) *
        limitingWeightOnPoints y (s + j.1) (s + j.1 + 1) := by
    norm_num [delta] at ⊢
    nlinarith
  have hadj := v21_adjacent_weight_le_localPairEnergy y s j
  have hp := v21_localPressure_nonneg y s hgap
  rw [localFp_eq]
  linarith

/-- The exact remaining compact region after the two elementary reductions:
all six gaps lie strictly above `0.89`, while their total span is below
`14.37`. -/
def V21HardCoreClaim : Prop :=
  ∀ (y : ℕ → ℝ) (s : ℕ),
    (∀ j : Fin 6, 0 ≤ windowGap y s j) →
    (∀ j : Fin 6, v17KernelCertPoint < windowGap y s j) →
    y (s+6) - y s < (1437 / 100 : ℝ) →
      delta ≤ localFp (limitingWeightOnPoints y) y s

/-- Once the compact hard core is proved, the universal article inequality
follows: large total span is settled by pressure, and any gap at most `0.89`
is settled by the internally certified adjacent kernel term. -/
theorem v21_article_of_hard_core
    (hsigned : V17KernelSignedCertPointClaim)
    (hcore : V21HardCoreClaim) :
    ArticleSevenPointInequality := by
  intro y s hgap
  by_cases hspan : (1437 / 100 : ℝ) ≤ y (s+6) - y s
  · exact v21_localFp_of_large_span y s hgap hspan
  · have hspanlt : y (s+6) - y s < (1437 / 100 : ℝ) := lt_of_not_ge hspan
    by_cases hsmall : ∃ j : Fin 6, windowGap y s j ≤ v17KernelCertPoint
    · rcases hsmall with ⟨j, hj⟩
      exact v21_localFp_of_small_gap hsigned y s hgap j hj
    · apply hcore y s hgap
      · intro j
        have hj : ¬ windowGap y s j ≤ v17KernelCertPoint := by
          intro h
          exact hsmall ⟨j, h⟩
        exact lt_of_not_ge hj
      · exact hspanlt

/-- Exact algebraic expansion of the historical seven-point functional. -/
theorem v21_localFp_eq_explicit (y : ℕ → ℝ) (s : ℕ) :
    localFp (limitingWeightOnPoints y) y s = v21ExplicitF y s := by
  simp only [localFp, localPressure, localPairEnergy, limitingWeightOnPoints,
    windowGap, v21ExplicitF]
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ]
  simp [pressure]
  ring

/-- The v21 target is exactly the historical external certificate frontier. -/
theorem v21_article_target_iff :
    ArchivedSevenPointClaim ↔ ArticleSevenPointInequality := by
  rfl

end HurtadoZeta23
