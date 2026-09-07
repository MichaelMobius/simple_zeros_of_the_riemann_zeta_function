import HurtadoZeta23.CriticalLatticeGeometry
import HurtadoZeta23.FiniteGridTruncation
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- The retained integer interval of the finite critical lattice. -/
def retainedIndexSet (kMin kMax : ℤ) : Finset ℤ :=
  Finset.Icc kMin kMax

/-- Left, middle, and right pieces of a finite set of integer indices relative
to the retained interval `[kMin,kMax]`. -/
def leftIndexPart (s : Finset ℤ) (kMin : ℤ) : Finset ℤ :=
  s.filter (fun k => k < kMin)

def middleIndexPart (s : Finset ℤ) (kMin kMax : ℤ) : Finset ℤ :=
  s.filter (fun k => kMin ≤ k ∧ k ≤ kMax)

def rightIndexPart (s : Finset ℤ) (kMax : ℤ) : Finset ℤ :=
  s.filter (fun k => kMax < k)

/-- Every integer belongs to exactly one of the three order regions when
`kMin ≤ kMax`. -/
lemma integer_region_trichotomy
    {kMin kMax k : ℤ} (hkk : kMin ≤ kMax) :
    k < kMin ∨ (kMin ≤ k ∧ k ≤ kMax) ∨ kMax < k := by
  omega

/-- Pointwise decomposition of an arbitrary summand according to the three
regions. -/
lemma summand_region_decomposition
    {β : Type*} [AddCommGroup β]
    {kMin kMax k : ℤ} (hkk : kMin ≤ kMax) (f : ℤ → β) :
    f k =
      (if k < kMin then f k else 0) +
      (if kMin ≤ k ∧ k ≤ kMax then f k else 0) +
      (if kMax < k then f k else 0) := by
  rcases integer_region_trichotomy (k := k) hkk with hL | hMR
  · have hnM : ¬ (kMin ≤ k ∧ k ≤ kMax) := by omega
    have hnR : ¬ kMax < k := by omega
    simp [hL, hnM, hnR]
  · rcases hMR with hM | hR
    · have hnL : ¬ k < kMin := by omega
      have hnR : ¬ kMax < k := by omega
      simp [hnL, hM, hnR]
    · have hnL : ¬ k < kMin := by omega
      have hnM : ¬ (kMin ≤ k ∧ k ≤ kMax) := by omega
      simp [hnL, hnM, hR]

/-- Exact finite-set partition.  This is purely algebraic/order-theoretic and
uses no convergence theorem. -/
theorem finite_sum_integer_partition
    {β : Type*} [AddCommGroup β]
    (f : ℤ → β) (s : Finset ℤ) {kMin kMax : ℤ}
    (hkk : kMin ≤ kMax) :
    Finset.sum s f =
      Finset.sum (leftIndexPart s kMin) f +
      Finset.sum (middleIndexPart s kMin kMax) f +
      Finset.sum (rightIndexPart s kMax) f := by
  classical

  have hpoint :
      Finset.sum s f =
        Finset.sum s
          (fun k =>
            (if k < kMin then f k else 0) +
            (if kMin ≤ k ∧ k ≤ kMax then f k else 0) +
            (if kMax < k then f k else 0)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact summand_region_decomposition hkk f

  have hsplit :
      Finset.sum s
          (fun k =>
            (if k < kMin then f k else 0) +
            (if kMin ≤ k ∧ k ≤ kMax then f k else 0) +
            (if kMax < k then f k else 0))
        =
      Finset.sum s (fun k => if k < kMin then f k else 0) +
      Finset.sum s (fun k => if kMin ≤ k ∧ k ≤ kMax then f k else 0) +
      Finset.sum s (fun k => if kMax < k then f k else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

  have hleft :
      Finset.sum (leftIndexPart s kMin) f =
        Finset.sum s (fun k => if k < kMin then f k else 0) := by
    unfold leftIndexPart
    exact Finset.sum_filter (fun k : ℤ => k < kMin) f

  have hmiddle :
      Finset.sum (middleIndexPart s kMin kMax) f =
        Finset.sum s
          (fun k => if kMin ≤ k ∧ k ≤ kMax then f k else 0) := by
    unfold middleIndexPart
    exact Finset.sum_filter (fun k : ℤ => kMin ≤ k ∧ k ≤ kMax) f

  have hright :
      Finset.sum (rightIndexPart s kMax) f =
        Finset.sum s (fun k => if kMax < k then f k else 0) := by
    unfold rightIndexPart
    exact Finset.sum_filter (fun k : ℤ => kMax < k) f

  rw [hpoint, hsplit, ← hleft, ← hmiddle, ← hright]

/-- On the retained interval itself, the middle piece is the whole set and
both omitted pieces are empty. -/
lemma retainedIndexSet_partition
    {kMin kMax : ℤ} (hkk : kMin ≤ kMax) :
    leftIndexPart (retainedIndexSet kMin kMax) kMin = ∅ ∧
    middleIndexPart (retainedIndexSet kMin kMax) kMin kMax =
      retainedIndexSet kMin kMax ∧
    rightIndexPart (retainedIndexSet kMin kMax) kMax = ∅ := by
  classical
  constructor
  · unfold leftIndexPart
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk
    have hkI : kMin ≤ k := by
      exact (Finset.mem_Icc.mp (by simpa [retainedIndexSet] using hk)).1
    exact not_lt_of_ge hkI
  constructor
  · unfold middleIndexPart
    apply Finset.filter_eq_self.mpr
    intro k hk
    exact Finset.mem_Icc.mp (by simpa [retainedIndexSet] using hk)
  · unfold rightIndexPart
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk
    have hkI : k ≤ kMax := by
      exact (Finset.mem_Icc.mp (by simpa [retainedIndexSet] using hk)).2
    exact not_lt_of_ge hkI

/-- The actual finite-grid overlap used in the paper is the sum over the
integer interval `[kMin,kMax]`. -/
def intervalFiniteGridOverlap
    (ϱ : ℝ → ℝ) (lam L w T τ τ' : ℝ) (kMin kMax : ℤ) : ℝ :=
  Finset.sum (retainedIndexSet kMin kMax)
    (fun k => phiDGridSummand ϱ lam L w T τ τ' k)

lemma intervalFiniteGridOverlap_eq_finiteGridOverlap
    (ϱ : ℝ → ℝ) (lam L w T τ τ' : ℝ) (kMin kMax : ℤ) :
    intervalFiniteGridOverlap ϱ lam L w T τ τ' kMin kMax =
      finiteGridOverlap ϱ lam L w T τ τ' (retainedIndexSet kMin kMax) := by
  simp [intervalFiniteGridOverlap, finiteGridOverlap]

/-- Finite-exhaustion version specialized to the actual `phiDGridSummand`. -/
theorem phiD_finite_exhaustion_partition
    (ϱ : ℝ → ℝ) (lam L w T τ τ' : ℝ)
    (s : Finset ℤ) {kMin kMax : ℤ} (hkk : kMin ≤ kMax) :
    Finset.sum s (phiDGridSummand ϱ lam L w T τ τ') =
      Finset.sum (leftIndexPart s kMin)
        (phiDGridSummand ϱ lam L w T τ τ') +
      Finset.sum (middleIndexPart s kMin kMax)
        (phiDGridSummand ϱ lam L w T τ τ') +
      Finset.sum (rightIndexPart s kMax)
        (phiDGridSummand ϱ lam L w T τ τ') := by
  exact finite_sum_integer_partition _ _ hkk

/-- Exact target identity for the infinite lattice decomposition.  The later
module `ExactTsumDecomposition` proves this from summability and the explicit
half-line equivalences. -/
def ExactInfiniteLatticeDecomposition
    (f : ℤ → ℝ) (kMin kMax : ℤ) : Prop :=
  (∑' k : ℤ, f k) =
    (∑' j : ℕ, f (kMin - 1 - Int.ofNat j)) +
    Finset.sum (retainedIndexSet kMin kMax) f +
    (∑' j : ℕ, f (kMax + 1 + Int.ofNat j))

end HurtadoZeta23
