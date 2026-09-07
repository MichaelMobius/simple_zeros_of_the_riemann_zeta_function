import HurtadoZeta23.InteriorBoundaryBridge
import Zeta23.RvM.NcountWindow
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Finset

namespace HurtadoZeta23

/-- Number of unit windows used to cover one interior boundary strip. -/
def interiorBoundaryUnitWindows (T : ℝ) : ℕ :=
  ⌈interiorBoundaryWidth T⌉₊

/--
Exact decomposition of an integer-length window into unit windows.

This is the finite bookkeeping analogue of the grouping used throughout
`Zeta23.Tail.Count`.
-/
theorem Ncount_unit_window_sum (a : ℝ) :
    ∀ n : ℕ,
      Zeta23.Ncount a (a + n) =
        ∑ i ∈ Finset.range n,
          Zeta23.Ncount (a + i) (a + i + 1) := by

  intro n

  induction n with

  | zero =>
      have hself :
          Zeta23.Ncount a a = 0 := by

        have hadd :=
          Zeta23.Ncount_add
            (a := a)
            (b := a)
            (c := a)
            le_rfl
            le_rfl

        omega

      simpa using hself

  | succ n ih =>

      have hn0 :
          (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)

      have h₁ :
          a ≤ a + (n : ℝ) := by
        linarith

      have h₂ :
          a + (n : ℝ)
            ≤
          a + ((n + 1 : ℕ) : ℝ) := by
        push_cast
        linarith

      have hadd :
          Zeta23.Ncount a (a + ((n + 1 : ℕ) : ℝ))
            =
          Zeta23.Ncount a (a + (n : ℝ))
            +
          Zeta23.Ncount
            (a + (n : ℝ))
            (a + ((n + 1 : ℕ) : ℝ)) := by
        exact Zeta23.Ncount_add h₁ h₂

      rw [hadd, ih, Finset.sum_range_succ]

      congr 1

      have hendpoint :
          a + ((n + 1 : ℕ) : ℝ)
            =
          a + (n : ℝ) + 1 := by
        push_cast
        ring

      rw [hendpoint]

/--
Apply the RvM unit-window local count term-by-term to an integer-length
window. No asymptotic estimate is used here.
-/
theorem Ncount_unit_window_sum_le_local
    {A₀ : ℝ}
    (hloc :
      ∀ t : ℝ,
        (Zeta23.Ncount t (t + 1) : ℝ)
          ≤
        A₀ * Real.log (|t| + 3))
    (a : ℝ)
    (n : ℕ) :
    (Zeta23.Ncount a (a + n) : ℝ)
      ≤
    ∑ i ∈ Finset.range n,
      A₀ * Real.log (|a + i| + 3) := by

  rw [Ncount_unit_window_sum]

  push_cast

  apply Finset.sum_le_sum

  intro i hi

  exact hloc (a + (i : ℝ))

/--
The real strip width is bounded by the ceiling number of unit windows.
-/
theorem interiorBoundaryWidth_le_unitWindows
    {T : ℝ}
    (_hwidth : 0 ≤ interiorBoundaryWidth T) :
    interiorBoundaryWidth T
      ≤
    (interiorBoundaryUnitWindows T : ℝ) := by

  unfold interiorBoundaryUnitWindows

  exact Nat.le_ceil (interiorBoundaryWidth T)

/--
Cover the left interior strip by the integer-length unit-window cover.
-/
theorem leftInteriorBoundary_le_unitCover
    {T : ℝ}
    (hwidth : 0 ≤ interiorBoundaryWidth T) :
    Zeta23.Ncount
        T
        (T + interiorBoundaryWidth T)
      ≤
    Zeta23.Ncount
        T
        (T + interiorBoundaryUnitWindows T) := by

  apply
    Zeta23.Ncount_mono
      (c := T)
      (d := T + interiorBoundaryUnitWindows T)

  · rfl

  ·
    have hw :=
      interiorBoundaryWidth_le_unitWindows hwidth

    linarith

/--
Cover the right interior strip by the corresponding integer-length window.
-/
theorem rightInteriorBoundary_le_unitCover
    {T : ℝ}
    (hwidth : 0 ≤ interiorBoundaryWidth T) :
    Zeta23.Ncount
        (2 * T - interiorBoundaryWidth T)
        (2 * T)
      ≤
    Zeta23.Ncount
        (2 * T - interiorBoundaryUnitWindows T)
        (2 * T) := by

  apply Zeta23.Ncount_mono

  ·
    have hw :=
      interiorBoundaryWidth_le_unitWindows hwidth

    linarith

  · rfl

/--
The exact local-count reduction for both interior strips.

Everything on its right side is now a finite sum of the published RvM
unit-window estimate. The only remaining work is elementary control of the
number of summands and of the logarithms in these two finite sums.
-/
theorem interiorBoundaryLoss_le_unit_window_logs
    {T A₀ : ℝ}
    (hwidth : 0 ≤ interiorBoundaryWidth T)
    (hloc :
      ∀ t : ℝ,
        (Zeta23.Ncount t (t + 1) : ℝ)
          ≤
        A₀ * Real.log (|t| + 3)) :
    interiorBoundaryLoss T
      ≤
    (∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
      A₀ * Real.log (|T + i| + 3))
      +
    (∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
      A₀ * Real.log
        (|2 * T - interiorBoundaryUnitWindows T + i| + 3)) := by

  unfold
    interiorBoundaryLoss
    interiorBoundaryCountNat

  have hL :=
    leftInteriorBoundary_le_unitCover hwidth

  have hR :=
    rightInteriorBoundary_le_unitCover hwidth

  have hLc :=
    Ncount_unit_window_sum_le_local
      hloc
      T
      (interiorBoundaryUnitWindows T)

  have hRc :=
    Ncount_unit_window_sum_le_local
      hloc
      (2 * T - interiorBoundaryUnitWindows T)
      (interiorBoundaryUnitWindows T)

  have hsumL :
      (Zeta23.Ncount
          T
          (T + interiorBoundaryWidth T) : ℝ)
        ≤
      ∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
        A₀ * Real.log (|T + i| + 3) := by

    have hLcast :
        (Zeta23.Ncount
            T
            (T + interiorBoundaryWidth T) : ℝ)
          ≤
        (Zeta23.Ncount
            T
            (T + interiorBoundaryUnitWindows T) : ℝ) := by
      exact_mod_cast hL

    exact hLcast.trans hLc

  have hRc' :
      (Zeta23.Ncount
          (2 * T - interiorBoundaryUnitWindows T)
          (2 * T) : ℝ)
        ≤
      ∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
        A₀ * Real.log
          (|2 * T - interiorBoundaryUnitWindows T + i| + 3) := by

    simpa using hRc

  have hsumR :
      (Zeta23.Ncount
          (2 * T - interiorBoundaryWidth T)
          (2 * T) : ℝ)
        ≤
      ∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
        A₀ * Real.log
          (|2 * T - interiorBoundaryUnitWindows T + i| + 3) := by

    have hRcast :
        (Zeta23.Ncount
            (2 * T - interiorBoundaryWidth T)
            (2 * T) : ℝ)
          ≤
        (Zeta23.Ncount
            (2 * T - interiorBoundaryUnitWindows T)
            (2 * T) : ℝ) := by
      exact_mod_cast hR

    exact hRcast.trans hRc'

  push_cast

  linarith

/--
Purely elementary envelope needed after
`interiorBoundaryLoss_le_unit_window_logs`.

It deliberately contains no zero-count information. Once this is
discharged, `InteriorBoundaryLocalCount` follows from Zeta23's published
`local_count`.

This structure contains real constants as data, so it lives in `Type`.
-/
structure InteriorBoundaryElementaryEnvelope where

  Cn : ℝ
  Clog : ℝ

  Cn_nonneg :
    0 ≤ Cn

  Clog_nonneg :
    0 ≤ Clog

  unitWindows_bound :
    ∀ᶠ T in atTop,
      (interiorBoundaryUnitWindows T : ℝ)
        ≤
      Cn * Zeta23.l T

  leftLog_bound :
    ∀ᶠ T in atTop,
      ∀ i < interiorBoundaryUnitWindows T,
        Real.log (|T + i| + 3)
          ≤
        Clog * Zeta23.l T

  rightLog_bound :
    ∀ᶠ T in atTop,
      ∀ i < interiorBoundaryUnitWindows T,
        Real.log
            (|2 * T - interiorBoundaryUnitWindows T + i| + 3)
          ≤
        Clog * Zeta23.l T

/--
Zeta23's unit local count plus the elementary ceiling/log envelope implies
the exact `O(l(T)^2)` package required by the retained-core bridge.
-/
def interiorBoundaryLocalCount_of_rvm
    (hE : InteriorBoundaryElementaryEnvelope) :
    InteriorBoundaryLocalCount := by

  let hlocal :=
    Zeta23.paperInputs_zeta.RvM.local_count

  let A₀ : ℝ :=
    Classical.choose hlocal

  have hA₀data :
      1 ≤ A₀ ∧
        ∀ t : ℝ,
          (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ)
            ≤
          A₀ * Real.log (|t| + 3) := by

    exact Classical.choose_spec hlocal

  have hA₀ :
      1 ≤ A₀ :=
    hA₀data.1

  have hA₀_nonneg :
      0 ≤ A₀ := by
    linarith

  have hloc :
      ∀ t : ℝ,
        (Zeta23.Ncount t (t + 1) : ℝ)
          ≤
        A₀ * Real.log (|t| + 3) := by

    intro t

    simpa using hA₀data.2 t

  refine
    {
      C :=
        2 * A₀ * hE.Cn * hE.Clog

      C_nonneg := ?_

      eventually_bound := ?_
    }

  ·
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (by norm_num)
            hA₀_nonneg)
          hE.Cn_nonneg)
        hE.Clog_nonneg

  ·
    filter_upwards
      [
        tendsto_zeta_l_atTop.eventually_ge_atTop 0,
        hE.unitWindows_bound,
        hE.leftLog_bound,
        hE.rightLog_bound
      ]
      with T hl hn hleft hright

    have hwidth :
        0 ≤ interiorBoundaryWidth T := by

      unfold interiorBoundaryWidth

      exact
        mul_nonneg
          (by positivity)
          hl

    have hbase :=
      interiorBoundaryLoss_le_unit_window_logs
        hwidth
        hloc

    have hleftsum :
        (∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
          A₀ * Real.log (|T + i| + 3))
          ≤
        A₀ *
          ((interiorBoundaryUnitWindows T : ℝ) *
            (hE.Clog * Zeta23.l T)) := by

      calc
        (∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
          A₀ * Real.log (|T + i| + 3))
            ≤
          ∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
            A₀ * (hE.Clog * Zeta23.l T) := by

              apply Finset.sum_le_sum

              intro i hi

              apply
                mul_le_mul_of_nonneg_left
                  (hleft i (Finset.mem_range.mp hi))
                  hA₀_nonneg

        _ =
          A₀ *
            ((interiorBoundaryUnitWindows T : ℝ) *
              (hE.Clog * Zeta23.l T)) := by

              simp only [
                Finset.sum_const,
                Finset.card_range,
                nsmul_eq_mul
              ]

              ring

    have hrightsum :
        (∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
          A₀ * Real.log
            (|2 * T - interiorBoundaryUnitWindows T + i| + 3))
          ≤
        A₀ *
          ((interiorBoundaryUnitWindows T : ℝ) *
            (hE.Clog * Zeta23.l T)) := by

      calc
        (∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
          A₀ * Real.log
            (|2 * T - interiorBoundaryUnitWindows T + i| + 3))
            ≤
          ∑ i ∈ Finset.range (interiorBoundaryUnitWindows T),
            A₀ * (hE.Clog * Zeta23.l T) := by

              apply Finset.sum_le_sum

              intro i hi

              apply
                mul_le_mul_of_nonneg_left
                  (hright i (Finset.mem_range.mp hi))
                  hA₀_nonneg

        _ =
          A₀ *
            ((interiorBoundaryUnitWindows T : ℝ) *
              (hE.Clog * Zeta23.l T)) := by

              simp only [
                Finset.sum_const,
                Finset.card_range,
                nsmul_eq_mul
              ]

              ring

    have hfirst :
        interiorBoundaryLoss T
          ≤
        2 * A₀ *
          ((interiorBoundaryUnitWindows T : ℝ) *
            (hE.Clog * Zeta23.l T)) := by

      linarith

    have hlog_nonneg :
        0 ≤ hE.Clog * Zeta23.l T := by

      exact
        mul_nonneg
          hE.Clog_nonneg
          hl

    have hwindow_step :
        (interiorBoundaryUnitWindows T : ℝ) *
            (hE.Clog * Zeta23.l T)
          ≤
        (hE.Cn * Zeta23.l T) *
            (hE.Clog * Zeta23.l T) := by

      exact
        mul_le_mul_of_nonneg_right
          hn
          hlog_nonneg

    have hcoef_nonneg :
        0 ≤ 2 * A₀ := by
      nlinarith

    have hsecond :
        2 * A₀ *
            ((interiorBoundaryUnitWindows T : ℝ) *
              (hE.Clog * Zeta23.l T))
          ≤
        2 * A₀ *
            ((hE.Cn * Zeta23.l T) *
              (hE.Clog * Zeta23.l T)) := by

      exact
        mul_le_mul_of_nonneg_left
          hwindow_step
          hcoef_nonneg

    calc
      interiorBoundaryLoss T
          ≤
        2 * A₀ *
          ((interiorBoundaryUnitWindows T : ℝ) *
            (hE.Clog * Zeta23.l T)) :=
        hfirst

      _ ≤
        2 * A₀ *
          ((hE.Cn * Zeta23.l T) *
            (hE.Clog * Zeta23.l T)) :=
        hsecond

      _ =
        (2 * A₀ * hE.Cn * hE.Clog) *
          (Zeta23.l T) ^ 2 := by
            ring

end HurtadoZeta23