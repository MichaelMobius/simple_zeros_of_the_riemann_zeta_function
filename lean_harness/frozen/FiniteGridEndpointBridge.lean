import HurtadoZeta23.DiscreteCentralityBridge
import Zeta23.ThmD.ParamsD
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Finite-grid endpoint rounding

For the article endpoint,
  d = floor(L T / (2 pi))
and the finite synthesis matrix uses rows `0, ..., d-1`.

This file proves that the last integer grid point is no more than two
critical steps below `2T`.  Combined with `DiscreteCentralityBridge`, this
removes the final endpoint-rounding hypothesis from the retained-block
centrality statement.
-/

/-- Integer index of the last row of the article critical grid. -/
def articleLastGridIndex (T : ℝ) : ℤ :=
  Int.ofNat (articleParams.d T) - 1

/-- `atD` has exactly the same grid cardinality, so this is also its last
integer row index. -/
theorem articleLastGridIndex_atD
    (T : ℝ) :
    articleLastGridIndex T =
      Int.ofNat ((articleParams.atD T).d T) - 1 := by
  unfold articleLastGridIndex
  rw [Zeta23.Params.atD_d]

/--
The last finite grid point lies at least `2T - 2h`.

The two-step loss is intentionally conservative and comes only from:
* `floor x > x - 1`;
* using row `d-1` rather than the point with index `d`.
-/
theorem articleLastGridPoint_lower
    {T : ℝ}
    (hl : 0 < Zeta23.l T) :
    2 * T - 2 * articleCriticalStep T
      ≤
    criticalGridPoint
      T
      (articleCriticalStep T)
      (articleLastGridIndex T) := by

  let L : ℝ := articleParams.L T
  let h : ℝ := articleCriticalStep T
  let x : ℝ := L * T / (2 * Real.pi)

  have hL : 0 < L := by
    dsimp [L]
    simpa using hl

  have hh : 0 < h := by
    dsimp [h]
    exact articleCriticalStep_pos hl

  have hfloor :
      x - 1 < (articleParams.d T : ℝ) := by
    dsimp [x]
    unfold Zeta23.Params.d
    simpa [L] using
      (Nat.sub_one_lt_floor
        (articleParams.L T * T / (2 * Real.pi)))

  have hx :
      x * h = T := by
    dsimp [x, h, L]
    unfold articleCriticalStep
    rw [← articleParams_L_eq_zeta_l T]

    have hL0 :
        articleParams.L T ≠ 0 := by
      exact ne_of_gt hL

    have hpi0 :
        (2 * Real.pi : ℝ) ≠ 0 := by
      positivity

    calc
      (articleParams.L T * T / (2 * Real.pi)) *
          (2 * Real.pi / articleParams.L T)
          =
        articleParams.L T * T / articleParams.L T := by
          field_simp [hpi0, hL0]

      _ = T := by
          apply (div_eq_iff hL0).2
          ring

  have hmul :
      (x - 1) * h
        <
      (articleParams.d T : ℝ) * h := by
    exact mul_lt_mul_of_pos_right hfloor hh

  have hd :
      T - h
        ≤
      (articleParams.d T : ℝ) * h := by
    have hrewrite :
        (x - 1) * h = T - h := by
      calc
        (x - 1) * h = x * h - h := by ring
        _ = T - h := by rw [hx]
    rw [hrewrite] at hmul
    exact le_of_lt hmul

  have hdlast :
      2 * T - 2 * h
        ≤
      T + ((articleParams.d T : ℝ) - 1) * h := by

    calc
      2 * T - 2 * h
          =
        T + ((T - h) - h) := by
          ring

      _ ≤
        T + (((articleParams.d T : ℝ) * h) - h) := by
          simpa [add_comm] using
            (add_le_add_left
              (sub_le_sub_right hd h)
              T)

      _ =
        T + ((articleParams.d T : ℝ) - 1) * h := by
          ring

  calc
    2 * T - 2 * articleCriticalStep T
        ≤
      T + ((articleParams.d T : ℝ) - 1) *
        articleCriticalStep T := by
          simpa [h] using hdlast

    _ =
      criticalGridPoint
        T
        (articleCriticalStep T)
        (articleLastGridIndex T) := by
          simp [criticalGridPoint, articleLastGridIndex]

/--
Every zero of a retained consecutive block satisfies literal finite-grid
centrality with the actual last matrix index.
-/
theorem consecutiveZero_articleGridCentrality
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i : Fin blockLength)
    {M : ℕ}
    (hM :
      (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2) :
    CriticalGridCentrality
      T
      (articleCriticalStep T)
      0
      (articleLastGridIndex T)
      M
      (consecutiveZero T s hs i).im := by

  exact
    consecutiveZero_criticalGridCentrality
      hl
      s
      hs
      i
      (articleLastGridPoint_lower hl)
      hM

/--
Pair form, ready to feed directly into the left/right p=4 omitted-tail
majorants.
-/
theorem consecutiveZero_pair_articleGridCentrality
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength)
    {M : ℕ}
    (hM :
      (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2) :
    CriticalGridCentrality
        T
        (articleCriticalStep T)
        0
        (articleLastGridIndex T)
        M
        (consecutiveZero T s hs i).im
      ∧
    CriticalGridCentrality
        T
        (articleCriticalStep T)
        0
        (articleLastGridIndex T)
        M
        (consecutiveZero T s hs j).im := by

  exact
    ⟨consecutiveZero_articleGridCentrality
        hl s hs i hM,
     consecutiveZero_articleGridCentrality
        hl s hs j hM⟩

end HurtadoZeta23
