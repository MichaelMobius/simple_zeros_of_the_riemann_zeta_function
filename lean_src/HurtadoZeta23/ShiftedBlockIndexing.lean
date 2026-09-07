import HurtadoZeta23.UnshiftedBlockPinching
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace HurtadoZeta23

/-!
# Shifted block indexing

Pure finite arithmetic for the shifted-block argument.

If `1 ≤ m ≤ N`, every valid start of a full length-`m` block,
`0 ≤ s < N - m + 1`, has a unique representation

  s = r + q*m

with `r < m` and `q < (N-r)/m`.

Thus the set of all consecutive full blocks is exactly the disjoint union of
the `m` shifted disjoint block families.
-/

/-- Start position belonging to residue `r` and quotient `q`. -/
def shiftedBlockStart
    {N m : ℕ}
    (r : Fin m)
    (q : Fin ((N - r.1) / m)) :
    ℕ :=
  r.1 + q.1 * m

/-- A residue/quotient pair always determines a full length-`m` block. -/
theorem shiftedBlockStart_add_le
    {N m : ℕ}
    (hm : 1 ≤ m)
    (r : Fin m)
    (q : Fin ((N - r.1) / m)) :
    shiftedBlockStart r q + m ≤ N := by

  have hm0 : 0 < m := by omega

  have hq :
      q.1 + 1 ≤ (N - r.1) / m :=
    Nat.succ_le_of_lt q.2

  have hmul :
      (q.1 + 1) * m ≤ N - r.1 :=
    (Nat.le_div_iff_mul_le hm0).1 hq

  unfold shiftedBlockStart

  have heq :
      r.1 + q.1 * m + m =
        r.1 + (q.1 + 1) * m := by
    ring

  rw [heq]

  omega

/-- Hence a residue/quotient pair gives an element of the ordinary sliding
start range `Fin (N-m+1)` whenever `m ≤ N`. -/
def shiftedBlockStartFin
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N)
    (r : Fin m)
    (q : Fin ((N - r.1) / m)) :
    Fin (N - m + 1) := by

  refine ⟨shiftedBlockStart r q, ?_⟩

  have hfull :=
    shiftedBlockStart_add_le hm r q

  omega

/-- Decomposition of a valid sliding start into residue and quotient. -/
noncomputable def slidingStartToShifted
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N)
    (s : Fin (N - m + 1)) :
    Σ r : Fin m, Fin ((N - r.1) / m) := by

  have hm0 : 0 < m := by omega

  let rNat : ℕ := s.1 % m
  let qNat : ℕ := s.1 / m

  have hr : rNat < m := by
    dsimp [rNat]
    exact Nat.mod_lt _ hm0

  let r : Fin m := ⟨rNat, hr⟩

  have hsfull :
      s.1 + m ≤ N := by
    omega

  have hdecomp :
      rNat + m * qNat = s.1 := by
    dsimp [rNat, qNat]
    exact Nat.mod_add_div s.1 m

  have hsum :
      rNat + (qNat + 1) * m ≤ N := by
    have heq :
        rNat + (qNat + 1) * m =
          s.1 + m := by
      rw [← hdecomp]
      ring
    rw [heq]
    exact hsfull

  have hmul :
      (qNat + 1) * m ≤ N - rNat := by
    omega

  have hqle :
      qNat + 1 ≤ (N - rNat) / m :=
    (Nat.le_div_iff_mul_le hm0).2 hmul

  have hq :
      qNat < (N - rNat) / m := by
    omega

  exact ⟨r, ⟨qNat, by simpa [r] using hq⟩⟩

/-- The natural map from a shifted residue/quotient pair to the corresponding
ordinary sliding start. -/
def shiftedToSlidingMap
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N) :
    (Σ r : Fin m, Fin ((N - r.1) / m))
      →
    Fin (N - m + 1) :=
  fun rq =>
    shiftedBlockStartFin hm hNm rq.1 rq.2

/-- The shifted representation is injective. -/
theorem shiftedToSlidingMap_injective
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N) :
    Function.Injective
      (shiftedToSlidingMap hm hNm) := by

  have hm0 : 0 < m := by omega

  intro a b hab
  rcases a with ⟨r, q⟩
  rcases b with ⟨r', q'⟩

  have hv := congrArg Fin.val hab

  change
    r.1 + q.1 * m =
      r'.1 + q'.1 * m
    at hv

  have hrval :
      r.1 = r'.1 := by

    have hmod :=
      congrArg (fun n : ℕ => n % m) hv

    simpa [
      Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt r.2,
      Nat.mod_eq_of_lt r'.2
    ] using hmod

  have hr : r = r' :=
    Fin.ext hrval

  subst r'

  have hqval :
      q.1 = q'.1 := by

    have hdiv :=
      congrArg (fun n : ℕ => n / m) hv

    have hleft :
        (r.1 + q.1 * m) / m = q.1 := by
      rw [Nat.add_mul_div_right r.1 q.1 hm0]
      rw [Nat.div_eq_of_lt r.2]
      simp

    have hright :
        (r.1 + q'.1 * m) / m = q'.1 := by
      rw [Nat.add_mul_div_right r.1 q'.1 hm0]
      rw [Nat.div_eq_of_lt r.2]
      simp

    rw [hleft, hright] at hdiv
    exact hdiv

  have hq : q = q' :=
    Fin.ext hqval

  subst q'
  rfl

/-- Every ordinary sliding start comes from a shifted residue/quotient pair. -/
theorem shiftedToSlidingMap_surjective
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N) :
    Function.Surjective
      (shiftedToSlidingMap hm hNm) := by

  have hm0 : 0 < m := by omega

  intro s

  let r : Fin m :=
    ⟨s.1 % m, Nat.mod_lt _ hm0⟩

  have hsfull :
      s.1 + m ≤ N := by
    omega

  have hdecomp :
      r.1 + m * (s.1 / m) = s.1 := by
    dsimp [r]
    exact Nat.mod_add_div s.1 m

  have hsum :
      r.1 + (s.1 / m + 1) * m ≤ N := by
    calc
      r.1 + (s.1 / m + 1) * m
          =
        (r.1 + m * (s.1 / m)) + m := by
            ring
      _ = s.1 + m := by
            rw [hdecomp]
      _ ≤ N := hsfull

  have hmul :
      (s.1 / m + 1) * m ≤ N - r.1 := by
    omega

  have hqle :
      s.1 / m + 1 ≤ (N - r.1) / m :=
    (Nat.le_div_iff_mul_le hm0).2 hmul

  have hq :
      s.1 / m < (N - r.1) / m := by
    omega

  let q : Fin ((N - r.1) / m) :=
    ⟨s.1 / m, hq⟩

  refine ⟨⟨r, q⟩, ?_⟩

  apply Fin.ext
  change r.1 + q.1 * m = s.1

  dsimp [r, q]

  simpa [Nat.mul_comm] using
    (Nat.mod_add_div s.1 m)

/-- Equivalence from shifted residue/quotient data to ordinary sliding starts. -/
noncomputable def shiftedToSlidingEquiv
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N) :
    (Σ r : Fin m, Fin ((N - r.1) / m))
      ≃
    Fin (N - m + 1) :=
  Equiv.ofBijective
    (shiftedToSlidingMap hm hNm)
    ⟨shiftedToSlidingMap_injective hm hNm,
     shiftedToSlidingMap_surjective hm hNm⟩

/-- The arithmetic equivalence underlying the `m` shifted decompositions. -/
noncomputable def slidingStartEquiv
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N) :
    Fin (N - m + 1)
      ≃
    (Σ r : Fin m, Fin ((N - r.1) / m)) :=
  (shiftedToSlidingEquiv hm hNm).symm

/-- Evaluating the inverse equivalence recovers the expected start
`r + q*m`. -/
@[simp] theorem slidingStartEquiv_symm_val
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N)
    (rq : Σ r : Fin m, Fin ((N - r.1) / m)) :
    ((slidingStartEquiv hm hNm).symm rq).1 =
      shiftedBlockStart rq.1 rq.2 := by
  rfl

/-- Finite-sum reindexing: summing over every consecutive full block is
identical to summing over the `m` shifted disjoint block families. -/
theorem sum_sliding_starts_eq_shifted
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N)
    (f : ℕ → ℝ) :
    (∑ s : Fin (N - m + 1), f s.1)
      =
    ∑ rq : (Σ r : Fin m, Fin ((N - r.1) / m)),
      f (shiftedBlockStart rq.1 rq.2) := by

  exact
    Fintype.sum_equiv
      (slidingStartEquiv hm hNm)
      (fun s : Fin (N - m + 1) => f s.1)
      (fun rq : (Σ r : Fin m, Fin ((N - r.1) / m)) =>
        f (shiftedBlockStart rq.1 rq.2))
      (by
        intro s
        apply congrArg f
        have h :=
          congrArg Fin.val
            ((slidingStartEquiv hm hNm).symm_apply_apply s)
        have hs :
            shiftedBlockStart
                (slidingStartEquiv hm hNm s).1
                (slidingStartEquiv hm hNm s).2
              =
            s.1 := by
          simpa only [slidingStartEquiv_symm_val] using h
        exact hs.symm)

/-- Sigma sums split as the expected outer residue sum and inner quotient
sum. -/
theorem sum_shifted_sigma
    {N m : ℕ}
    (f :
      (Σ r : Fin m, Fin ((N - r.1) / m)) → ℝ) :
    (∑ rq : (Σ r : Fin m, Fin ((N - r.1) / m)), f rq)
      =
    ∑ r : Fin m,
      ∑ q : Fin ((N - r.1) / m), f ⟨r, q⟩ := by
  exact Fintype.sum_sigma f

/-- Convenient nested-sum form of the shifted-start reindexing identity. -/
theorem sum_sliding_starts_eq_nested_shifted
    {N m : ℕ}
    (hm : 1 ≤ m)
    (hNm : m ≤ N)
    (f : ℕ → ℝ) :
    (∑ s : Fin (N - m + 1), f s.1)
      =
    ∑ r : Fin m,
      ∑ q : Fin ((N - r.1) / m),
        f (r.1 + q.1 * m) := by

  rw [sum_sliding_starts_eq_shifted hm hNm f]
  rw [sum_shifted_sigma]
  rfl

end HurtadoZeta23
