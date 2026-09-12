import HurtadoZeta23.V21OneBodyB1Localization
import HurtadoZeta23.V21OneBodyB2LowerSlivers
import HurtadoZeta23.V21OneBodyCentralExclusionTable
import HurtadoZeta23.V21OneBodyRootTail
import HurtadoZeta23.V21OneBodyPressureCaps
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Exact refined survivor basins for a type-A coordinate (positions 0,5). -/
def v21TypeABasins (x : ℝ) : Prop :=
  ((955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ)) ∨
  ((1792 / 1000 : ℝ) < x ∧ x < (2258 / 1000 : ℝ)) ∨
  ((2612 / 1000 : ℝ) < x ∧ x < (3396 / 1000 : ℝ)) ∨
  ((3502 / 1000 : ℝ) < x ∧ x < (4465 / 1000 : ℝ)) ∨
  ((4500 / 1000 : ℝ) < x ∧ x < (5466 / 1000 : ℝ)) ∨
  ((5500 / 1000 : ℝ) < x ∧ x < (6413 / 1000 : ℝ)) ∨
  ((6576 / 1000 : ℝ) < x ∧ x < (7270 / 1000 : ℝ))

/-- Exact refined survivor basins for a type-B coordinate (positions 1,4). -/
def v21TypeBBasins (x : ℝ) : Prop :=
  ((955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ)) ∨
  ((1798 / 1000 : ℝ) < x ∧ x < (2249 / 1000 : ℝ)) ∨
  ((2637 / 1000 : ℝ) < x ∧ x < (3358 / 1000 : ℝ)) ∨
  ((3568 / 1000 : ℝ) < x ∧ x < (4375 / 1000 : ℝ)) ∨
  ((4611 / 1000 : ℝ) < x ∧ x < (5285 / 1000 : ℝ))

/-- Exact refined survivor basins for a type-C coordinate (positions 2,3). -/
def v21TypeCBasins (x : ℝ) : Prop :=
  ((955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ)) ∨
  ((1797 / 1000 : ℝ) < x ∧ x < (2251 / 1000 : ℝ)) ∨
  ((2633 / 1000 : ℝ) < x ∧ x < (3365 / 1000 : ℝ)) ∨
  ((3556 / 1000 : ℝ) < x ∧ x < (4392 / 1000 : ℝ)) ∨
  ((4580 / 1000 : ℝ) < x ∧ x < (5322 / 1000 : ℝ)) ∨
  ((5793 / 1000 : ℝ) < x ∧ x < (6078 / 1000 : ℝ))

/- Explicit basin constructors keep the right-associated disjunction structure
stable across Lean elaborator versions. -/
private lemma v21_typeA_basin1 {x : ℝ}
    (h : (955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inl h

private lemma v21_typeA_basin2 {x : ℝ}
    (h : (1792 / 1000 : ℝ) < x ∧ x < (2258 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inr (Or.inl h)

private lemma v21_typeA_basin3 {x : ℝ}
    (h : (2612 / 1000 : ℝ) < x ∧ x < (3396 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inr (Or.inr (Or.inl h))

private lemma v21_typeA_basin4 {x : ℝ}
    (h : (3502 / 1000 : ℝ) < x ∧ x < (4465 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private lemma v21_typeA_basin5 {x : ℝ}
    (h : (4500 / 1000 : ℝ) < x ∧ x < (5466 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private lemma v21_typeA_basin6 {x : ℝ}
    (h : (5500 / 1000 : ℝ) < x ∧ x < (6413 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

private lemma v21_typeA_basin7 {x : ℝ}
    (h : (6576 / 1000 : ℝ) < x ∧ x < (7270 / 1000 : ℝ)) : v21TypeABasins x := by
  unfold v21TypeABasins
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

private lemma v21_typeB_basin1 {x : ℝ}
    (h : (955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ)) : v21TypeBBasins x := by
  unfold v21TypeBBasins
  exact Or.inl h

private lemma v21_typeB_basin2 {x : ℝ}
    (h : (1798 / 1000 : ℝ) < x ∧ x < (2249 / 1000 : ℝ)) : v21TypeBBasins x := by
  unfold v21TypeBBasins
  exact Or.inr (Or.inl h)

private lemma v21_typeB_basin3 {x : ℝ}
    (h : (2637 / 1000 : ℝ) < x ∧ x < (3358 / 1000 : ℝ)) : v21TypeBBasins x := by
  unfold v21TypeBBasins
  exact Or.inr (Or.inr (Or.inl h))

private lemma v21_typeB_basin4 {x : ℝ}
    (h : (3568 / 1000 : ℝ) < x ∧ x < (4375 / 1000 : ℝ)) : v21TypeBBasins x := by
  unfold v21TypeBBasins
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private lemma v21_typeB_basin5 {x : ℝ}
    (h : (4611 / 1000 : ℝ) < x ∧ x < (5285 / 1000 : ℝ)) : v21TypeBBasins x := by
  unfold v21TypeBBasins
  exact Or.inr (Or.inr (Or.inr (Or.inr h)))

private lemma v21_typeC_basin1 {x : ℝ}
    (h : (955 / 1000 : ℝ) < x ∧ x < (1158 / 1000 : ℝ)) : v21TypeCBasins x := by
  unfold v21TypeCBasins
  exact Or.inl h

private lemma v21_typeC_basin2 {x : ℝ}
    (h : (1797 / 1000 : ℝ) < x ∧ x < (2251 / 1000 : ℝ)) : v21TypeCBasins x := by
  unfold v21TypeCBasins
  exact Or.inr (Or.inl h)

private lemma v21_typeC_basin3 {x : ℝ}
    (h : (2633 / 1000 : ℝ) < x ∧ x < (3365 / 1000 : ℝ)) : v21TypeCBasins x := by
  unfold v21TypeCBasins
  exact Or.inr (Or.inr (Or.inl h))

private lemma v21_typeC_basin4 {x : ℝ}
    (h : (3556 / 1000 : ℝ) < x ∧ x < (4392 / 1000 : ℝ)) : v21TypeCBasins x := by
  unfold v21TypeCBasins
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private lemma v21_typeC_basin5 {x : ℝ}
    (h : (4580 / 1000 : ℝ) < x ∧ x < (5322 / 1000 : ℝ)) : v21TypeCBasins x := by
  unfold v21TypeCBasins
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private lemma v21_typeC_basin6 {x : ℝ}
    (h : (5793 / 1000 : ℝ) < x ∧ x < (6078 / 1000 : ℝ)) : v21TypeCBasins x := by
  unfold v21TypeCBasins
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

lemma v21_gapBands_nonneg {x : ℝ} (h : v21GapBands x) : 0 ≤ x := by
  rcases h with h | h | h <;> nlinarith

/-- Type-A localization: a sub-threshold one-body value in the coarse survivor
bands must lie in exactly one of the seven refined A basins. -/
theorem v21_oneBody_localize_A {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hbands : v21GapBands x)
    (hsmall : v21OneBody j x < (2081 / 1000000 : ℝ)) :
    v21TypeABasins x := by
  have hx0 := v21_gapBands_nonneg hbands
  have hcap := v21_oneBody_pressure_cap_A hx0 hp hsmall
  rcases hbands with h1 | h2 | h3
  · exact v21_typeA_basin1 (v21_oneBody_B1_localize_A hp h1.1 h1.2 hsmall)
  · have hlo : (1792 / 1000 : ℝ) < x := by
      by_contra h
      have hge := v21_oneBody_A_B2_lower_sliver hp h2.1 (le_of_not_gt h)
      linarith
    have hhi : x < (2258 / 1000 : ℝ) := by
      by_contra h
      have hge := v21_oneBody_A_gap2 hp (le_of_not_gt h) (by nlinarith [h2.2])
      linarith
    exact v21_typeA_basin2 ⟨hlo, hhi⟩
  · have h2612 : (2612 / 1000 : ℝ) < x := by
      by_contra h
      have hge := v21_oneBody_A_gap2 hp (by nlinarith [h3.1]) (le_of_not_gt h)
      linarith
    by_cases h3396 : x < (3396 / 1000 : ℝ)
    · exact v21_typeA_basin3 ⟨h2612, h3396⟩
    · have h3502 : (3502 / 1000 : ℝ) < x := by
        by_contra h
        have hge := v21_oneBody_A_gap3 hp (le_of_not_gt h3396) (le_of_not_gt h)
        linarith
      by_cases h4465 : x < (4465 / 1000 : ℝ)
      · exact v21_typeA_basin4 ⟨h3502, h4465⟩
      · have h4500 : (4500 / 1000 : ℝ) < x := by
          by_contra h
          have hge := v21_oneBody_A_gap4 hp (le_of_not_gt h4465) (le_of_not_gt h)
          linarith
        by_cases h5466 : x < (5466 / 1000 : ℝ)
        · exact v21_typeA_basin5 ⟨h4500, h5466⟩
        · have h5500 : (5500 / 1000 : ℝ) < x := by
            by_contra h
            have hge := v21_oneBody_A_gap5 hp (le_of_not_gt h5466) (le_of_not_gt h)
            linarith
          by_cases h6413 : x < (6413 / 1000 : ℝ)
          · exact v21_typeA_basin6 ⟨h5500, h6413⟩
          · have h6576 : (6576 / 1000 : ℝ) < x := by
              by_contra h
              have hge := v21_oneBody_A_gap6 hp (le_of_not_gt h6413) (le_of_not_gt h)
              linarith
            by_cases h7270 : x < (7270 / 1000 : ℝ)
            · exact v21_typeA_basin7 ⟨h6576, h7270⟩
            · have hge := v21_oneBody_A_tail7 hp (le_of_not_gt h7270) hcap.le
              linarith

/-- Type-B localization into the five refined B basins. -/
theorem v21_oneBody_localize_B {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hbands : v21GapBands x)
    (hsmall : v21OneBody j x < (2189 / 1000000 : ℝ)) :
    v21TypeBBasins x := by
  have hx0 := v21_gapBands_nonneg hbands
  have hcap := v21_oneBody_pressure_cap_B hx0 hp hsmall
  rcases hbands with h1 | h2 | h3
  · exact v21_typeB_basin1 (v21_oneBody_B1_localize_B hp h1.1 h1.2 hsmall)
  · have hlo : (1798 / 1000 : ℝ) < x := by
      by_contra h
      have hge := v21_oneBody_B_B2_lower_sliver hp h2.1 (le_of_not_gt h)
      linarith
    have hhi : x < (2249 / 1000 : ℝ) := by
      by_contra h
      have hge := v21_oneBody_B_gap2 hp (le_of_not_gt h) (by nlinarith [h2.2])
      linarith
    exact v21_typeB_basin2 ⟨hlo, hhi⟩
  · have h2637 : (2637 / 1000 : ℝ) < x := by
      by_contra h
      have hge := v21_oneBody_B_gap2 hp (by nlinarith [h3.1]) (le_of_not_gt h)
      linarith
    by_cases h3358 : x < (3358 / 1000 : ℝ)
    · exact v21_typeB_basin3 ⟨h2637, h3358⟩
    · have h3568 : (3568 / 1000 : ℝ) < x := by
        by_contra h
        have hge := v21_oneBody_B_gap3 hp (le_of_not_gt h3358) (le_of_not_gt h)
        linarith
      by_cases h4375 : x < (4375 / 1000 : ℝ)
      · exact v21_typeB_basin4 ⟨h3568, h4375⟩
      · have h4611 : (4611 / 1000 : ℝ) < x := by
          by_contra h
          have hge := v21_oneBody_B_gap4 hp (le_of_not_gt h4375) (le_of_not_gt h)
          linarith
        by_cases h5285 : x < (5285 / 1000 : ℝ)
        · exact v21_typeB_basin5 ⟨h4611, h5285⟩
        · have h5780 : (5780 / 1000 : ℝ) < x := by
            by_contra h
            have hge := v21_oneBody_B_gap5a hp (le_of_not_gt h5285) (le_of_not_gt h)
            linarith
          have h5850 : (5850 / 1000 : ℝ) < x := by
            by_contra h
            have hge := v21_oneBody_B_gap5b hp h5780.le (le_of_not_gt h)
            linarith
          have hge := v21_oneBody_B_tail5 hp h5850.le hcap.le
          linarith

/-- Type-C localization into the six refined C basins. -/
theorem v21_oneBody_localize_C {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hbands : v21GapBands x)
    (hsmall : v21OneBody j x < (2170 / 1000000 : ℝ)) :
    v21TypeCBasins x := by
  have hx0 := v21_gapBands_nonneg hbands
  have hcap := v21_oneBody_pressure_cap_C hx0 hp hsmall
  rcases hbands with h1 | h2 | h3
  · exact v21_typeC_basin1 (v21_oneBody_B1_localize_C hp h1.1 h1.2 hsmall)
  · have hlo : (1797 / 1000 : ℝ) < x := by
      by_contra h
      have hge := v21_oneBody_C_B2_lower_sliver hp h2.1 (le_of_not_gt h)
      linarith
    have hhi : x < (2251 / 1000 : ℝ) := by
      by_contra h
      have hge := v21_oneBody_C_gap2 hp (le_of_not_gt h) (by nlinarith [h2.2])
      linarith
    exact v21_typeC_basin2 ⟨hlo, hhi⟩
  · have h2633 : (2633 / 1000 : ℝ) < x := by
      by_contra h
      have hge := v21_oneBody_C_gap2 hp (by nlinarith [h3.1]) (le_of_not_gt h)
      linarith
    by_cases h3365 : x < (3365 / 1000 : ℝ)
    · exact v21_typeC_basin3 ⟨h2633, h3365⟩
    · have h3556 : (3556 / 1000 : ℝ) < x := by
        by_contra h
        have hge := v21_oneBody_C_gap3 hp (le_of_not_gt h3365) (le_of_not_gt h)
        linarith
      by_cases h4392 : x < (4392 / 1000 : ℝ)
      · exact v21_typeC_basin4 ⟨h3556, h4392⟩
      · have h4580 : (4580 / 1000 : ℝ) < x := by
          by_contra h
          have hge := v21_oneBody_C_gap4 hp (le_of_not_gt h4392) (le_of_not_gt h)
          linarith
        by_cases h5322 : x < (5322 / 1000 : ℝ)
        · exact v21_typeC_basin5 ⟨h4580, h5322⟩
        · have h5750 : (5750 / 1000 : ℝ) < x := by
            by_contra h
            have hge := v21_oneBody_C_gap5a hp (le_of_not_gt h5322) (le_of_not_gt h)
            linarith
          have h5793 : (5793 / 1000 : ℝ) < x := by
            by_contra h
            have hge := v21_oneBody_C_gap5b hp h5750.le (le_of_not_gt h)
            linarith
          by_cases h6078 : x < (6078 / 1000 : ℝ)
          · exact v21_typeC_basin6 ⟨h5793, h6078⟩
          · have hge := v21_oneBody_C_tail6 hp (le_of_not_gt h6078) hcap.le
            linarith

end HurtadoZeta23
