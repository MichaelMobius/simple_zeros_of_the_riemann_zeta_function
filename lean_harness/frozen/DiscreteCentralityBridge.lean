import HurtadoZeta23.RetainedCentralityBridge
import HurtadoZeta23.CriticalLatticeGeometry
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Continuous-to-discrete centrality bridge

The article deletes continuous boundary strips of width `2π l(T)`, which is
exactly `articleCriticalStep T * l(T)^2`.

The actual finite matrix, however, is indexed by `k = 0, ..., d-1`, so its
rightmost grid point can lie slightly to the left of `2T`.  This file isolates
that rounding seam explicitly.

If the rightmost grid point is at most two grid steps short of `2T`, then any
continuous margin `step * (M + 2)` implies the literal
`CriticalGridCentrality ... M` required by the p=4 tail machinery.
-/

/-- The article critical step is exactly the `hgrid` of the endpoint
Montgomery--Taylor parameter family. -/
theorem articleCriticalStep_eq_hgrid
    (T : ℝ) :
    articleCriticalStep T =
      (articleParams.atD T).hgrid T := by
  rw [Zeta23.Params.atD_hgrid]
  unfold articleCriticalStep Zeta23.Params.hgrid
  rw [articleParams_L_eq_zeta_l]

/-- `criticalGridPoint` agrees with the article's `tau` convention. -/
theorem criticalGridPoint_eq_article_tau
    (T : ℝ)
    (k : ℤ) :
    criticalGridPoint T (articleCriticalStep T) k =
      (articleParams.atD T).tau T k := by
  unfold criticalGridPoint Zeta23.Params.tau
  rw [← articleCriticalStep_eq_hgrid T]

/--
Generic continuous-to-discrete centrality lemma.

The left finite-grid endpoint is exactly `T`.  On the right we allow the
last retained grid point to be as much as two grid steps below `2T`.
Consequently a continuous margin of `(M+2)` cells yields `M` literal discrete
centrality cells.
-/
theorem criticalGridCentrality_of_continuous_band
    {T step width τ : ℝ}
    {kMax : ℤ}
    {M : ℕ}
    (hstep : 0 < step)
    (hleft :
      T + width ≤ τ)
    (hright :
      τ ≤ 2 * T - width)
    (hkMax :
      2 * T - 2 * step
        ≤ criticalGridPoint T step kMax)
    (hmargin :
      step * ((M : ℝ) + 2) ≤ width) :
    CriticalGridCentrality
      T step 0 kMax M τ := by

  refine ⟨hstep, ?_, ?_⟩

  ·
    have hM :
        step * (M : ℝ) ≤ width := by
      have htwo :
          0 ≤ 2 * step := by
        positivity
      nlinarith

    unfold criticalGridPoint
    simp only [Int.cast_zero, zero_mul, add_zero]

    linarith

  ·
    have hM :
        step * (M : ℝ) + 2 * step ≤ width := by
      nlinarith

    linarith

/--
Specialization to one zero in a consecutive retained block.

The only remaining geometric inputs are:

* a lower bound locating the last matrix grid point within two steps of `2T`;
* a natural margin `M` satisfying `M+2 ≤ l(T)^2`.
-/
theorem consecutiveZero_criticalGridCentrality
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength)
    {kMax : ℤ}
    {M : ℕ}
    (hkMax :
      2 * T - 2 * articleCriticalStep T
        ≤
      criticalGridPoint
        T
        (articleCriticalStep T)
        kMax)
    (hM :
      (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2) :
    CriticalGridCentrality
      T
      (articleCriticalStep T)
      0
      kMax
      M
      (consecutiveZero T s hs i).im := by

  have hstep :
      0 < articleCriticalStep T :=
    articleCriticalStep_pos hl

  have hband :=
    consecutiveZero_im_central
      T s hs i

  have hmargin0 :
      articleCriticalStep T * ((M : ℝ) + 2)
        ≤
      articleCriticalStep T * (Zeta23.l T) ^ 2 := by

    exact
      mul_le_mul_of_nonneg_left
        hM
        (le_of_lt hstep)

  have hmargin :
      articleCriticalStep T * ((M : ℝ) + 2)
        ≤
      interiorBoundaryWidth T := by

    calc
      articleCriticalStep T * ((M : ℝ) + 2)
          ≤
        articleCriticalStep T * (Zeta23.l T) ^ 2 :=
          hmargin0

      _ =
        interiorBoundaryWidth T :=
          articleCriticalStep_mul_l_sq hl

  exact
    criticalGridCentrality_of_continuous_band
      hstep
      hband.1
      hband.2
      hkMax
      hmargin

/--
Pair version used directly by the two-sided p=4 overlap tail.
-/
theorem consecutiveZero_pair_criticalGridCentrality
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength)
    {kMax : ℤ}
    {M : ℕ}
    (hkMax :
      2 * T - 2 * articleCriticalStep T
        ≤
      criticalGridPoint
        T
        (articleCriticalStep T)
        kMax)
    (hM :
      (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2) :
    CriticalGridCentrality
        T
        (articleCriticalStep T)
        0
        kMax
        M
        (consecutiveZero T s hs i).im
      ∧
    CriticalGridCentrality
        T
        (articleCriticalStep T)
        0
        kMax
        M
        (consecutiveZero T s hs j).im := by

  exact
    ⟨consecutiveZero_criticalGridCentrality
        hl s hs i hkMax hM,
     consecutiveZero_criticalGridCentrality
        hl s hs j hkMax hM⟩

end HurtadoZeta23
