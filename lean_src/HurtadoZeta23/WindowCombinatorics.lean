import HurtadoZeta23.PositionWeights
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped BigOperators

/--
For an indexed pair `a < b`, these are all integer starting positions of a
seven-point window that can contain both endpoints.  Boundary restrictions
from a finite `m`-point configuration are imposed separately below.
-/
def pairContainingStarts (a b : ℤ) : Finset ℤ :=
  Finset.Icc (b - 6) a

/-- Admissible seven-point windows inside an `m`-point configuration. -/
def admissiblePairStarts (m a b : ℤ) : Finset ℤ :=
  pairContainingStarts a b ∩ Finset.Icc 0 (m - 7)

lemma admissiblePairStarts_subset (m a b : ℤ) :
    admissiblePairStarts m a b ⊆ pairContainingStarts a b := by
  exact Finset.inter_subset_left

/--
If the pair is separated by at most six gaps, the *untruncated* family of
seven-point windows containing it has exactly `7 - (b-a)` elements.
-/
lemma pairContainingStarts_card_int {a b : ℤ} (hsep : b - a ≤ 6) :
    ((pairContainingStarts a b).card : ℤ) = 7 - (b - a) := by
  have hle : b - 6 ≤ a + 1 := by omega
  change ((Finset.Icc (b - 6) a).card : ℤ) = 7 - (b - a)
  rw [Int.card_Icc_of_le (b - 6) a hle]
  ring

/--
Boundary truncation can only reduce the number of windows containing a pair.
This is the exact counting statement used in Pressure redistribution.
-/
lemma admissiblePairStarts_card_le {m a b : ℤ} (hsep : b - a ≤ 6) :
    ((admissiblePairStarts m a b).card : ℤ) ≤ 7 - (b - a) := by
  have hcardNat :
      (admissiblePairStarts m a b).card ≤ (pairContainingStarts a b).card :=
    Finset.card_le_card (admissiblePairStarts_subset m a b)
  have hcardInt :
      ((admissiblePairStarts m a b).card : ℤ) ≤
        ((pairContainingStarts a b).card : ℤ) := by
    exact_mod_cast hcardNat
  calc
    ((admissiblePairStarts m a b).card : ℤ)
        ≤ ((pairContainingStarts a b).card : ℤ) := hcardInt
    _ = 7 - (b - a) := pairContainingStarts_card_int hsep

/--
The accumulated coefficient of a fixed pair in all seven-point windows.
For a pair separated by `r=b-a` gaps, every appearance carries `2/(7-r)`.
-/
def pairAccumulatedCoefficient (m a b : ℤ) : ℝ :=
  ((admissiblePairStarts m a b).card : ℝ) *
    (2 / (((7 - (b - a) : ℤ) : ℝ)))

/--
A fixed pair separated by `1 ≤ r ≤ 6` gaps receives total coefficient at most
`2` after summing all consecutive seven-point windows.
-/
lemma pair_accumulated_coefficient_le_two
    {m a b : ℤ} (hpos : 1 ≤ b - a) (hsep : b - a ≤ 6) :
    pairAccumulatedCoefficient m a b ≤ 2 := by
  have hcardZ := admissiblePairStarts_card_le (m := m) (a := a) (b := b) hsep
  have hcardR :
      ((admissiblePairStarts m a b).card : ℝ) ≤
        (((7 - (b - a) : ℤ) : ℝ)) := by
    exact_mod_cast hcardZ
  have hdenZ : (0 : ℤ) < 7 - (b - a) := by omega
  have hdenR : (0 : ℝ) < (((7 - (b - a) : ℤ) : ℝ)) := by
    exact_mod_cast hdenZ
  have hfactor :
      0 ≤ (2 : ℝ) / (((7 - (b - a) : ℤ) : ℝ)) :=
    div_nonneg (by norm_num) hdenR.le
  unfold pairAccumulatedCoefficient
  calc
    ((admissiblePairStarts m a b).card : ℝ) *
          (2 / (((7 - (b - a) : ℤ) : ℝ)))
        ≤ (((7 - (b - a) : ℤ) : ℝ)) *
          (2 / (((7 - (b - a) : ℤ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hcardR hfactor
    _ = 2 := by field_simp [ne_of_gt hdenR]

/--
If the global gap has index `q` and occupies relative gap position `j` in a
seven-point window, the starting index of that window is forced to be `q-j`.
-/
def gapWindowStart (q : ℤ) (j : Fin 6) : ℤ :=
  q - (j : ℕ)

/-- A fixed global gap can occupy a given relative position in at most one window. -/
lemma gapWindowStart_injective (q : ℤ) : Function.Injective (gapWindowStart q) := by
  intro i j hij
  apply Fin.ext
  dsimp [gapWindowStart] at hij
  omega

/-- Relative gap positions that actually correspond to a window inside the block. -/
def activeGapPositions (m q : ℤ) : Finset (Fin 6) :=
  Finset.univ.filter fun j =>
    0 ≤ gapWindowStart q j ∧ gapWindowStart q j ≤ m - 7

/-- Accumulated position-weighted pressure on one fixed global gap. -/
def gapPressureCoefficient (m q : ℤ) : ℝ :=
  ∑ j ∈ activeGapPositions m q, pressure j

lemma gapPressureCoefficient_nonneg (m q : ℤ) :
    0 ≤ gapPressureCoefficient m q := by
  unfold gapPressureCoefficient
  exact Finset.sum_nonneg fun j hj => pressure_nonneg j

/--
The nonuniform pressure distribution has the same global cost as the uniform
one: every fixed global gap accumulates at most `sum_j p_j = beta`.
-/
lemma gap_pressure_coefficient_le_beta (m q : ℤ) :
    gapPressureCoefficient m q ≤ beta := by
  unfold gapPressureCoefficient
  calc
    ∑ j ∈ activeGapPositions m q, pressure j
        ≤ ∑ j : Fin 6, pressure j := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _)
            (by
              intro j hj hjnot
              exact pressure_nonneg j)
    _ = beta := pressure_sum

/-- The elementary telescoping identity turning total gap length into span. -/
lemma telescoping_gap_sum (y : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ Finset.range n, (y (q + 1) - y q)) = y n - y 0 := by
  exact Finset.sum_range_sub y n

/--
Once every individual redistributed gap coefficient is bounded by `beta`, the
whole pressure contribution is bounded by `beta * span`.
-/
lemma total_gap_pressure_le_span
    {m : ℕ} (hm : 1 ≤ m) (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1)) :
    (∑ q ∈ Finset.range (m - 1),
        gapPressureCoefficient (m : ℤ) q * (y (q + 1) - y q))
      ≤ beta * (y (m - 1) - y 0) := by
  calc
    (∑ q ∈ Finset.range (m - 1),
        gapPressureCoefficient (m : ℤ) q * (y (q + 1) - y q))
        ≤ ∑ q ∈ Finset.range (m - 1),
            beta * (y (q + 1) - y q) := by
          apply Finset.sum_le_sum
          intro q hq
          have hq_lt : q < m - 1 := Finset.mem_range.mp hq
          have hgap : 0 ≤ y (q + 1) - y q := sub_nonneg.mpr (hmono q hq_lt)
          exact mul_le_mul_of_nonneg_right
            (gap_pressure_coefficient_le_beta (m : ℤ) q) hgap
    _ = beta * (∑ q ∈ Finset.range (m - 1), (y (q + 1) - y q)) := by
          rw [Finset.mul_sum]
    _ = beta * (y (m - 1) - y 0) := by
          rw [telescoping_gap_sum]


/-- Integer indices of the points in an `m`-point block. -/
def blockIndices (m : ℤ) : Finset ℤ :=
  Finset.Icc 0 (m - 1)

/-- All ordered index-pairs `a < b` inside the block. -/
def orderedBlockPairs (m : ℤ) : Finset (ℤ × ℤ) :=
  (blockIndices m ×ˢ blockIndices m).filter fun ab => ab.1 < ab.2

/-- Pairs that can occur together in a seven-point local window. -/
def nearBlockPairs (m : ℤ) : Finset (ℤ × ℤ) :=
  (orderedBlockPairs m).filter fun ab => ab.2 - ab.1 ≤ 6

lemma nearBlockPairs_subset (m : ℤ) :
    nearBlockPairs m ⊆ orderedBlockPairs m := by
  intro ab hab
  exact (Finset.mem_filter.mp hab).1

/-- The pair contribution after grouping all local-window terms by global pair. -/
def groupedLocalPairContribution
    (m : ℤ) (w : ℤ → ℤ → ℝ) : ℝ :=
  ∑ ab ∈ nearBlockPairs m,
    pairAccumulatedCoefficient m ab.1 ab.2 * w ab.1 ab.2

/-- The global pair energy `2 * sum_{a<b} w(a,b)`. -/
def globalPairEnergy
    (m : ℤ) (w : ℤ → ℤ → ℝ) : ℝ :=
  2 * ∑ ab ∈ orderedBlockPairs m, w ab.1 ab.2

/--
After local terms are grouped by their global pair, the counting lemma implies
that their entire contribution is at most the global pair energy.  This is the
pair-side inequality in Proposition Pressure redistribution.
-/
lemma grouped_local_pair_contribution_le_energy
    (m : ℤ) (w : ℤ → ℤ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) :
    groupedLocalPairContribution m w ≤ globalPairEnergy m w := by
  have hlocal :
      groupedLocalPairContribution m w
        ≤ ∑ ab ∈ nearBlockPairs m, 2 * w ab.1 ab.2 := by
    unfold groupedLocalPairContribution
    apply Finset.sum_le_sum
    intro ab hab
    have hnear := Finset.mem_filter.mp hab
    have hord := Finset.mem_filter.mp hnear.1
    have hlt : ab.1 < ab.2 := hord.2
    have hsep : ab.2 - ab.1 ≤ 6 := hnear.2
    have hpos : 1 ≤ ab.2 - ab.1 := by omega
    exact mul_le_mul_of_nonneg_right
      (pair_accumulated_coefficient_le_two
        (m := m) (a := ab.1) (b := ab.2) hpos hsep)
      (hw ab.1 ab.2)
  have hsum :
      (∑ ab ∈ nearBlockPairs m, w ab.1 ab.2)
        ≤ ∑ ab ∈ orderedBlockPairs m, w ab.1 ab.2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (nearBlockPairs_subset m)
      (by
        intro ab hab habnot
        exact hw ab.1 ab.2)
  calc
    groupedLocalPairContribution m w
        ≤ ∑ ab ∈ nearBlockPairs m, 2 * w ab.1 ab.2 := hlocal
    _ = 2 * (∑ ab ∈ nearBlockPairs m, w ab.1 ab.2) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * (∑ ab ∈ orderedBlockPairs m, w ab.1 ab.2) := by
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = globalPairEnergy m w := by rfl

end HurtadoZeta23
