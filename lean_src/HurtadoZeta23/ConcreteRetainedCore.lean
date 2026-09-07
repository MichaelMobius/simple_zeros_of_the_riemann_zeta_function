import HurtadoZeta23.ConcreteStableSeam
import HurtadoZeta23.SpanGeometry
import HurtadoZeta23.InteriorBoundaryElementary
import Zeta23.Statement.SeamClosed
import Zeta23.Defs.Counting
import Mathlib.Data.Set.Card
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Set

namespace HurtadoZeta23

/-!
# Concrete retained simple-zero core

This file removes two remaining abstract pieces from `RetainedCoreBridge`.

* `articleCentralRetentionCounts` is built from the literal set of simple
  critical-line zeta zeros in `(T,2T]`, after deleting the two interior strips
  of width `interiorBoundaryWidth T`.
* `articleRvMSpanInputs` uses the universal sampling span
  `T*l(T)/(2*pi)` directly.  Thus no artificial `firstOrd`/`lastOrd`
  witnesses are required.

No certificate or Gram pinching is used here.
-/

/-- The exact set counted by `N0simple T (2*T)`. -/
def dyadicSimpleCriticalSet (T : ℝ) : Set ℂ :=
  Zeta23.zerosIn T (2 * T)
    ∩ {ρ : ℂ | ρ.re = 1 / 2}
    ∩ {ρ : ℂ | Zeta23.zeroMult ρ = 1}

/-- The central ordinary-ordinate band left after deleting the two
`L^2`-cell strips used by the compact-overlap argument. -/
def retainedOrdinateBand (T : ℝ) : Set ℂ :=
  {ρ : ℂ |
    T + interiorBoundaryWidth T ≤ ρ.im ∧
    ρ.im ≤ 2 * T - interiorBoundaryWidth T}

/-- Simple critical-line zeros retained in the central band. -/
def retainedSimpleCriticalSet (T : ℝ) : Set ℂ :=
  dyadicSimpleCriticalSet T ∩ retainedOrdinateBand T

/-- Simple critical-line zeros discarded at the two interior strips. -/
def removedSimpleCriticalSet (T : ℝ) : Set ℂ :=
  dyadicSimpleCriticalSet T \ retainedOrdinateBand T

lemma dyadicSimpleCriticalSet_finite (T : ℝ) :
    (dyadicSimpleCriticalSet T).Finite := by
  exact
    (Zeta23.zerosIn_finite T (2 * T)).subset
      (by
        intro ρ hρ
        exact hρ.1.1)

lemma retainedSimpleCriticalSet_finite (T : ℝ) :
    (retainedSimpleCriticalSet T).Finite := by
  exact
    (dyadicSimpleCriticalSet_finite T).inter_of_left
      (retainedOrdinateBand T)

lemma removedSimpleCriticalSet_finite (T : ℝ) :
    (removedSimpleCriticalSet T).Finite := by
  exact
    (dyadicSimpleCriticalSet_finite T).sdiff

/-- The full simple set decomposes exactly as retained plus removed. -/
theorem retained_add_removed_eq_N0simple (T : ℝ) :
    (retainedSimpleCriticalSet T).ncard
      + (removedSimpleCriticalSet T).ncard
      =
    Zeta23.N0simple T (2 * T) := by

  have h :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard
      (dyadicSimpleCriticalSet T)
      (retainedOrdinateBand T)
      (dyadicSimpleCriticalSet_finite T)

  simpa [
    retainedSimpleCriticalSet,
    removedSimpleCriticalSet,
    dyadicSimpleCriticalSet,
    Zeta23.N0simple
  ] using h

/-- Every removed simple critical-line zero belongs to one of the two
ordinary-ordinate boundary windows. -/
theorem removedSimpleCriticalSet_subset_boundary_union (T : ℝ) :
    removedSimpleCriticalSet T
      ⊆
    Zeta23.zerosIn T (T + interiorBoundaryWidth T)
      ∪
    Zeta23.zerosIn
      (2 * T - interiorBoundaryWidth T) (2 * T) := by

  intro ρ hρ

  have hfull : ρ ∈ dyadicSimpleCriticalSet T := hρ.1
  have hnot : ρ ∉ retainedOrdinateBand T := hρ.2

  have hzero : ρ ∈ Zeta23.zerosIn T (2 * T) :=
    hfull.1.1

  change
    Zeta23.IsNontrivialZero ρ ∧
      T < ρ.im ∧
      ρ.im ≤ 2 * T
    at hzero

  change
    ¬ (T + interiorBoundaryWidth T ≤ ρ.im ∧
       ρ.im ≤ 2 * T - interiorBoundaryWidth T)
    at hnot

  rcases hzero with ⟨hz, hTlo, hThi⟩

  by_cases hleft :
      ρ.im < T + interiorBoundaryWidth T

  · left
    change
      Zeta23.IsNontrivialZero ρ ∧
        T < ρ.im ∧
        ρ.im ≤ T + interiorBoundaryWidth T
    exact ⟨hz, hTlo, le_of_lt hleft⟩

  · right

    have hlower :
        T + interiorBoundaryWidth T ≤ ρ.im :=
      le_of_not_gt hleft

    have hright :
        2 * T - interiorBoundaryWidth T < ρ.im := by
      apply lt_of_not_ge
      intro hupper
      exact hnot ⟨hlower, hupper⟩

    change
      Zeta23.IsNontrivialZero ρ ∧
        2 * T - interiorBoundaryWidth T < ρ.im ∧
        ρ.im ≤ 2 * T

    exact ⟨hz, hright, hThi⟩

/-- Cardinality of the removed simple set is bounded by the multiplicity
count of the two boundary windows. -/
theorem removedSimpleCriticalSet_ncard_le_boundary (T : ℝ) :
    (removedSimpleCriticalSet T).ncard
      ≤ interiorBoundaryCountNat T := by

  let L :=
    Zeta23.zerosIn T (T + interiorBoundaryWidth T)

  let R :=
    Zeta23.zerosIn
      (2 * T - interiorBoundaryWidth T) (2 * T)

  have hLf : L.Finite := by
    dsimp [L]
    exact Zeta23.zerosIn_finite _ _

  have hRf : R.Finite := by
    dsimp [R]
    exact Zeta23.zerosIn_finite _ _

  have hsub :
      removedSimpleCriticalSet T ⊆ L ∪ R := by
    simpa [L, R] using
      removedSimpleCriticalSet_subset_boundary_union T

  have hmono :
      (removedSimpleCriticalSet T).ncard
        ≤ (L ∪ R).ncard :=
    Set.ncard_le_ncard hsub (hLf.union hRf)

  have hunion :
      (L ∪ R).ncard ≤ L.ncard + R.ncard :=
    Set.ncard_union_le L R

  have hLN :
      L.ncard
        ≤
      Zeta23.Ncount T (T + interiorBoundaryWidth T) := by
    change
      Zeta23.Ndist T (T + interiorBoundaryWidth T)
        ≤
      Zeta23.Ncount T (T + interiorBoundaryWidth T)
    exact
      (Zeta23.trivial_chain₀
        T (T + interiorBoundaryWidth T)).2.2.2.2.2

  have hRN :
      R.ncard
        ≤
      Zeta23.Ncount
        (2 * T - interiorBoundaryWidth T) (2 * T) := by
    change
      Zeta23.Ndist
          (2 * T - interiorBoundaryWidth T) (2 * T)
        ≤
      Zeta23.Ncount
          (2 * T - interiorBoundaryWidth T) (2 * T)
    exact
      (Zeta23.trivial_chain₀
        (2 * T - interiorBoundaryWidth T) (2 * T)).2.2.2.2.2

  calc
    (removedSimpleCriticalSet T).ncard
        ≤ (L ∪ R).ncard := hmono
    _ ≤ L.ncard + R.ncard := hunion
    _ ≤
        Zeta23.Ncount T (T + interiorBoundaryWidth T)
          +
        Zeta23.Ncount
          (2 * T - interiorBoundaryWidth T) (2 * T) :=
      Nat.add_le_add hLN hRN
    _ = interiorBoundaryCountNat T := by
      rfl

/-- The concrete central-retention package required by the final assembly. -/
def articleCentralRetentionCounts :
    CentralRetentionCounts :=
  {
    retainedCount :=
      fun T => (retainedSimpleCriticalSet T).ncard

    removedCount :=
      fun T => (removedSimpleCriticalSet T).ncard

    decomposition :=
      Eventually.of_forall
        retained_add_removed_eq_N0simple

    removed_le_boundary :=
      Eventually.of_forall
        removedSimpleCriticalSet_ncard_le_boundary
  }

@[simp] theorem articleCentralRetentionCounts_retainedReal (T : ℝ) :
    articleCentralRetentionCounts.retainedReal T =
      ((retainedSimpleCriticalSet T).ncard : ℝ) := by
  rfl

/--
For shifted pinching it is enough to use the universal upper bound on the
normalized span of points in `[T,2T]`.  This avoids introducing arbitrary
endpoint choices for an empty/small retained set.
-/
def articleRvMSpanInputs :
    RvMSpanInputs :=
  {
    span := samplingSpanScale
    geomErr := samplingToRvMErr

    geom_bound :=
      Eventually.of_forall
        samplingSpanScale_le_rvmMain_add_err

    geomErr_small_TlogT :=
      samplingToRvMErr_small_TlogT
  }

@[simp] theorem articleRvMSpanInputs_span (T : ℝ) :
    articleRvMSpanInputs.span T = samplingSpanScale T := by
  rfl

/-- The span error in the concrete package is already `o(T log T)`. -/
theorem articleRvMSpanInputs_totalErr_small :
    articleRvMSpanInputs.totalErr
      =o[atTop]
    (fun T : ℝ => T * Zeta23.l T) :=
  articleRvMSpanInputs.totalErr_small_TlogT

end HurtadoZeta23
