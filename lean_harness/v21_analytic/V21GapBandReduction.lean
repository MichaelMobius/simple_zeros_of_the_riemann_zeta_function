import HurtadoZeta23.V21UniformGapExclusionsAnalytic
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Every one-body coordinate contribution is dominated by the full six-gap
functional once the six gaps are nonnegative. -/
theorem v21_minOneBody_le_gapF_each
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) (h2 : 0 ≤ g2)
    (h3 : 0 ≤ g3) (h4 : 0 ≤ g4) (h5 : 0 ≤ g5) :
    v21MinOneBody g0 ≤ v21GapF g0 g1 g2 g3 g4 g5 ∧
    v21MinOneBody g1 ≤ v21GapF g0 g1 g2 g3 g4 g5 ∧
    v21MinOneBody g2 ≤ v21GapF g0 g1 g2 g3 g4 g5 ∧
    v21MinOneBody g3 ≤ v21GapF g0 g1 g2 g3 g4 g5 ∧
    v21MinOneBody g4 ≤ v21GapF g0 g1 g2 g3 g4 g5 ∧
    v21MinOneBody g5 ≤ v21GapF g0 g1 g2 g3 g4 g5 := by
  have hp0 : 0 ≤ pressure (0 : Fin 6) * g0 :=
    mul_nonneg (pressure_nonneg (0 : Fin 6)) h0
  have hp1 : 0 ≤ pressure (1 : Fin 6) * g1 :=
    mul_nonneg (pressure_nonneg (1 : Fin 6)) h1
  have hp2 : 0 ≤ pressure (2 : Fin 6) * g2 :=
    mul_nonneg (pressure_nonneg (2 : Fin 6)) h2
  have hp3 : 0 ≤ pressure (3 : Fin 6) * g3 :=
    mul_nonneg (pressure_nonneg (3 : Fin 6)) h3
  have hp4 : 0 ≤ pressure (4 : Fin 6) * g4 :=
    mul_nonneg (pressure_nonneg (4 : Fin 6)) h4
  have hp5 : 0 ≤ pressure (5 : Fin 6) * g5 :=
    mul_nonneg (pressure_nonneg (5 : Fin 6)) h5

  have hw0 := limitingWeight_nonneg g0
  have hw1 := limitingWeight_nonneg g1
  have hw2 := limitingWeight_nonneg g2
  have hw3 := limitingWeight_nonneg g3
  have hw4 := limitingWeight_nonneg g4
  have hw5 := limitingWeight_nonneg g5

  have hpair2 :
      0 ≤ (2 / 5 : ℝ) *
        (limitingWeight (g0 + g1) +
         limitingWeight (g1 + g2) +
         limitingWeight (g2 + g3) +
         limitingWeight (g3 + g4) +
         limitingWeight (g4 + g5)) := by
    have h01 := limitingWeight_nonneg (g0 + g1)
    have h12 := limitingWeight_nonneg (g1 + g2)
    have h23 := limitingWeight_nonneg (g2 + g3)
    have h34 := limitingWeight_nonneg (g3 + g4)
    have h45 := limitingWeight_nonneg (g4 + g5)
    nlinarith
  have hpair3 :
      0 ≤ (1 / 2 : ℝ) *
        (limitingWeight (g0 + g1 + g2) +
         limitingWeight (g1 + g2 + g3) +
         limitingWeight (g2 + g3 + g4) +
         limitingWeight (g3 + g4 + g5)) := by
    have h012 := limitingWeight_nonneg (g0 + g1 + g2)
    have h123 := limitingWeight_nonneg (g1 + g2 + g3)
    have h234 := limitingWeight_nonneg (g2 + g3 + g4)
    have h345 := limitingWeight_nonneg (g3 + g4 + g5)
    nlinarith
  have hpair4 :
      0 ≤ (2 / 3 : ℝ) *
        (limitingWeight (g0 + g1 + g2 + g3) +
         limitingWeight (g1 + g2 + g3 + g4) +
         limitingWeight (g2 + g3 + g4 + g5)) := by
    have h0123 := limitingWeight_nonneg (g0 + g1 + g2 + g3)
    have h1234 := limitingWeight_nonneg (g1 + g2 + g3 + g4)
    have h2345 := limitingWeight_nonneg (g2 + g3 + g4 + g5)
    nlinarith
  have hpair5a := limitingWeight_nonneg (g0 + g1 + g2 + g3 + g4)
  have hpair5b := limitingWeight_nonneg (g1 + g2 + g3 + g4 + g5)
  have hpair6 :
      0 ≤ 2 * limitingWeight (g0 + g1 + g2 + g3 + g4 + g5) := by
    nlinarith [limitingWeight_nonneg (g0 + g1 + g2 + g3 + g4 + g5)]

  have hone0 :
      (1 / 3 : ℝ) * limitingWeight g0 ≤
        (1 / 3 : ℝ) *
          (limitingWeight g0 + limitingWeight g1 + limitingWeight g2 +
           limitingWeight g3 + limitingWeight g4 + limitingWeight g5) := by
    nlinarith
  have hone1 :
      (1 / 3 : ℝ) * limitingWeight g1 ≤
        (1 / 3 : ℝ) *
          (limitingWeight g0 + limitingWeight g1 + limitingWeight g2 +
           limitingWeight g3 + limitingWeight g4 + limitingWeight g5) := by
    nlinarith
  have hone2 :
      (1 / 3 : ℝ) * limitingWeight g2 ≤
        (1 / 3 : ℝ) *
          (limitingWeight g0 + limitingWeight g1 + limitingWeight g2 +
           limitingWeight g3 + limitingWeight g4 + limitingWeight g5) := by
    nlinarith
  have hone3 :
      (1 / 3 : ℝ) * limitingWeight g3 ≤
        (1 / 3 : ℝ) *
          (limitingWeight g0 + limitingWeight g1 + limitingWeight g2 +
           limitingWeight g3 + limitingWeight g4 + limitingWeight g5) := by
    nlinarith
  have hone4 :
      (1 / 3 : ℝ) * limitingWeight g4 ≤
        (1 / 3 : ℝ) *
          (limitingWeight g0 + limitingWeight g1 + limitingWeight g2 +
           limitingWeight g3 + limitingWeight g4 + limitingWeight g5) := by
    nlinarith
  have hone5 :
      (1 / 3 : ℝ) * limitingWeight g5 ≤
        (1 / 3 : ℝ) *
          (limitingWeight g0 + limitingWeight g1 + limitingWeight g2 +
           limitingWeight g3 + limitingWeight g4 + limitingWeight g5) := by
    nlinarith

  have hm0 := v21_minOneBody_le_coordinate (0 : Fin 6) h0
  have hm1 := v21_minOneBody_le_coordinate (1 : Fin 6) h1
  have hm2 := v21_minOneBody_le_coordinate (2 : Fin 6) h2
  have hm3 := v21_minOneBody_le_coordinate (3 : Fin 6) h3
  have hm4 := v21_minOneBody_le_coordinate (4 : Fin 6) h4
  have hm5 := v21_minOneBody_le_coordinate (5 : Fin 6) h5

  unfold v21GapF
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Any strict counterexample in the compact hard core must put every gap in
one of the three survivor bands. -/
theorem v21_gap_bands_of_counterexample
    (hfilter : V21UniformGapFilterClaim)
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v17KernelCertPoint < g0)
    (h1 : v17KernelCertPoint < g1)
    (h2 : v17KernelCertPoint < g2)
    (h3 : v17KernelCertPoint < g3)
    (h4 : v17KernelCertPoint < g4)
    (h5 : v17KernelCertPoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ))
    (hbad : v21GapF g0 g1 g2 g3 g4 g5 < delta) :
    v21GapBands g0 ∧ v21GapBands g1 ∧ v21GapBands g2 ∧
    v21GapBands g3 ∧ v21GapBands g4 ∧ v21GapBands g5 := by
  have hc0 : (0 : ℝ) ≤ g0 := by
    have : (0 : ℝ) < v17KernelCertPoint := by norm_num [v17KernelCertPoint]
    exact le_of_lt (this.trans h0)
  have hc1 : (0 : ℝ) ≤ g1 := by
    have : (0 : ℝ) < v17KernelCertPoint := by norm_num [v17KernelCertPoint]
    exact le_of_lt (this.trans h1)
  have hc2 : (0 : ℝ) ≤ g2 := by
    have : (0 : ℝ) < v17KernelCertPoint := by norm_num [v17KernelCertPoint]
    exact le_of_lt (this.trans h2)
  have hc3 : (0 : ℝ) ≤ g3 := by
    have : (0 : ℝ) < v17KernelCertPoint := by norm_num [v17KernelCertPoint]
    exact le_of_lt (this.trans h3)
  have hc4 : (0 : ℝ) ≤ g4 := by
    have : (0 : ℝ) < v17KernelCertPoint := by norm_num [v17KernelCertPoint]
    exact le_of_lt (this.trans h4)
  have hc5 : (0 : ℝ) ≤ g5 := by
    have : (0 : ℝ) < v17KernelCertPoint := by norm_num [v17KernelCertPoint]
    exact le_of_lt (this.trans h5)

  rcases v21_hard_core_individual_upper g0 g1 g2 g3 g4 g5
      h0 h1 h2 h3 h4 h5 hsum with
    ⟨hu0, hu1, hu2, hu3, hu4, hu5⟩
  rcases v21_minOneBody_le_gapF_each g0 g1 g2 g3 g4 g5
      hc0 hc1 hc2 hc3 hc4 hc5 with
    ⟨hl0, hl1, hl2, hl3, hl4, hl5⟩

  have hs0 : v21MinOneBody g0 < delta := hl0.trans_lt hbad
  have hs1 : v21MinOneBody g1 < delta := hl1.trans_lt hbad
  have hs2 : v21MinOneBody g2 < delta := hl2.trans_lt hbad
  have hs3 : v21MinOneBody g3 < delta := hl3.trans_lt hbad
  have hs4 : v21MinOneBody g4 < delta := hl4.trans_lt hbad
  have hs5 : v21MinOneBody g5 < delta := hl5.trans_lt hbad

  exact ⟨hfilter g0 h0 hu0 hs0,
    hfilter g1 h1 hu1 hs1,
    hfilter g2 h2 hu2 hs2,
    hfilter g3 h3 hu3 hs3,
    hfilter g4 h4 hu4 hs4,
    hfilter g5 h5 hu5 hs5⟩

/-- Analytic specialization: the endpoint/curvature proof supplies the filter,
so every hypothetical compact counterexample is reduced to a finite band
pattern. -/
theorem v21_gap_bands_of_analytic_counterexample
    (g0 g1 g2 g3 g4 g5 : ℝ)
    (h0 : v17KernelCertPoint < g0)
    (h1 : v17KernelCertPoint < g1)
    (h2 : v17KernelCertPoint < g2)
    (h3 : v17KernelCertPoint < g3)
    (h4 : v17KernelCertPoint < g4)
    (h5 : v17KernelCertPoint < g5)
    (hsum : g0 + g1 + g2 + g3 + g4 + g5 < (1437 / 100 : ℝ))
    (hbad : v21GapF g0 g1 g2 g3 g4 g5 < delta) :
    v21GapBands g0 ∧ v21GapBands g1 ∧ v21GapBands g2 ∧
    v21GapBands g3 ∧ v21GapBands g4 ∧ v21GapBands g5 := by
  exact v21_gap_bands_of_counterexample
    (v21_uniform_filter_of_exclusions v21_uniform_gap_exclusions_analytic)
    g0 g1 g2 g3 g4 g5 h0 h1 h2 h3 h4 h5 hsum hbad

end HurtadoZeta23
