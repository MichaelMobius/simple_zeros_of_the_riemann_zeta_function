import HurtadoZeta23.FiniteGridTruncation
import Zeta23.ThmD.BridgeD
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- The scalar p=4 majorant used for the omitted critical-lattice tail. -/
def p4Majorant (n : ℕ) : ℝ :=
  1 / ((n : ℝ) ^ 4)

/--
The p=4 majorant is summable; this is the standard p-series theorem
from Mathlib.
-/
theorem summable_p4Majorant :
    Summable p4Majorant := by
  unfold p4Majorant
  simpa using
    (Real.summable_one_div_nat_pow (p := 4)).2
      (by norm_num)

/--
A compact way to record that the retained points are at least `M` grid cells
from a chosen finite-grid endpoint.

The paper eventually takes `M = L^2`.
-/
def EndpointCentrality
    (step : ℝ)
    (M : ℕ)
    (τ endpoint : ℝ) : Prop :=
  0 < step ∧
    step * M ≤ |τ - endpoint|

/--
The `r^{-2}` Fourier decay from an admissible Zeta23 window, rewritten in a
form convenient for a common lower bound `D ≤ |r|`.
-/
theorem vHatR_decay_from_distance
    {v : ℝ → ℝ}
    {L w c D r : ℝ}
    (hW : Zeta23.AdmWindow v L w c)
    (hD : 0 < D)
    (hr : D ≤ |r|) :
    |Zeta23.AdmWindow.vHatR v r|
      ≤ (c / w) / D ^ 2 := by

  have hwpos : 0 < w :=
    hW.w_pos

  have hD0 : 0 ≤ D :=
    le_of_lt hD

  have hr0 : 0 ≤ |r| :=
    abs_nonneg r

  have hsq :
      D ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs r]
    nlinarith

  have hdec :
      |Zeta23.AdmWindow.vHatR v r| * r ^ 2
        ≤ c / w :=
    hW.abs_vHatR_mul_sq_le r

  have hnon :
      0 ≤ |Zeta23.AdmWindow.vHatR v r| :=
    abs_nonneg _

  have hmul :
      |Zeta23.AdmWindow.vHatR v r| * D ^ 2
        ≤ c / w := by
    calc
      |Zeta23.AdmWindow.vHatR v r| * D ^ 2
          ≤
        |Zeta23.AdmWindow.vHatR v r| * r ^ 2 := by
          exact
            mul_le_mul_of_nonneg_left
              hsq
              hnon

      _ ≤ c / w :=
        hdec

  rw [le_div_iff₀ (sq_pos_of_pos hD)]

  simpa [mul_comm] using hmul

/--
Product form of the preceding decay.

If both Fourier arguments are at least `D` from zero, their product is
controlled by a common `D^{-4}` majorant.
-/
theorem vHatR_product_decay_from_distance
    {v : ℝ → ℝ}
    {L w c D r s : ℝ}
    (hW : Zeta23.AdmWindow v L w c)
    (hD : 0 < D)
    (hr : D ≤ |r|)
    (hs : D ≤ |s|) :
    |Zeta23.AdmWindow.vHatR v r *
        Zeta23.AdmWindow.vHatR v s|
      ≤ ((c / w) ^ 2) / D ^ 4 := by

  have h1 :=
    vHatR_decay_from_distance
      hW hD hr

  have h2 :=
    vHatR_decay_from_distance
      hW hD hs

  have hcw :
      0 ≤ c / w := by
    have hzero :=
      hW.abs_vHatR_mul_sq_le 0
    simpa using hzero

  have hupper :
      0 ≤ (c / w) / D ^ 2 := by
    exact
      div_nonneg
        hcw
        (sq_nonneg D)

  rw [abs_mul]

  have hprod :
      |Zeta23.AdmWindow.vHatR v r| *
          |Zeta23.AdmWindow.vHatR v s|
        ≤
      ((c / w) / D ^ 2) *
          ((c / w) / D ^ 2) := by

    exact
      mul_le_mul
        h1
        h2
        (abs_nonneg _)
        hupper

  calc
    |Zeta23.AdmWindow.vHatR v r| *
        |Zeta23.AdmWindow.vHatR v s|
        ≤
      ((c / w) / D ^ 2) *
        ((c / w) / D ^ 2) :=
      hprod

    _ =
      ((c / w) ^ 2) / D ^ 4 := by
        field_simp [ne_of_gt hD]

/--
Abstract uniform half-tail domination.

This is the exact shape obtained once an omitted grid point `n` cells past
the endpoint is known to put both Fourier arguments at distance at least
`step * n` from zero.
-/
def UniformHalfTailMajorized
    (summand : ℕ → ℝ)
    (C step : ℝ)
    (M : ℕ) : Prop :=
  0 < step ∧
  0 ≤ C ∧
  ∀ n : ℕ,
    M ≤ n →
      |summand n|
        ≤ C / (step ^ 4 * (n : ℝ) ^ 4)

/--
The Zeta-specific analytic content of finite-grid truncation has now been
reduced to geometry plus the standard p=4 series.

After proving a lower bound on both Fourier arguments,
`abs_vHatR_mul_sq_le` supplies this majorization.
-/
theorem phiD_omitted_term_majorized
    {ϱ : ℝ → ℝ}
    {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    {r s D : ℝ}
    (hD : 0 < D)
    (hr : D ≤ |r|)
    (hs : D ≤ |s|) :
    |Zeta23.AdmWindow.vHatR
          (Zeta23.ThmD.phiD ϱ lam L w) r *
        Zeta23.AdmWindow.vHatR
          (Zeta23.ThmD.phiD ϱ lam L w) s|
      ≤
    (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2) / D ^ 4 := by

  exact
    vHatR_product_decay_from_distance
      (Zeta23.ThmD.admWindow_phiD
        hϱ h0 h1 hw hwL)
      hD
      hr
      hs

/--
The remaining geometric statement for the left or right omitted half-grid.

It is deliberately explicit: centrality by `M = L^2` cells and bounded
normalized separation must imply a common lower bound `step*n` for both
Fourier arguments.
-/
def HalfGridDistanceGeometry
    (step : ℝ)
    (M : ℕ)
    (r s : ℕ → ℝ) : Prop :=
  0 < step ∧
  ∀ n : ℕ,
    M ≤ n →
      step * n ≤ |r n| ∧
      step * n ≤ |s n|

/--
Geometry plus Zeta23's Fourier decay gives a genuine p=4 majorant for every
omitted term.

The hypothesis `1 ≤ M` is necessary: the p=4 majorant has denominator `n^4`,
so the omitted tail must begin at a positive index. In the application
`M = L^2`, this is exactly the intended regime.
-/
theorem phiD_half_tail_p4_majorant
    {ϱ : ℝ → ℝ}
    {lam L w step : ℝ}
    {M : ℕ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    {r s : ℕ → ℝ}
    (hM : 1 ≤ M)
    (hgeom : HalfGridDistanceGeometry step M r s) :
    UniformHalfTailMajorized
      (fun n =>
        Zeta23.AdmWindow.vHatR
            (Zeta23.ThmD.phiD ϱ lam L w)
            (r n) *
          Zeta23.AdmWindow.vHatR
            (Zeta23.ThmD.phiD ϱ lam L w)
            (s n))
      (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2)
      step
      M := by

  rcases hgeom with
    ⟨hstep, hgeom⟩

  have hc_nonneg :
      0 ≤
        ((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2 := by
    exact sq_nonneg _

  refine
    ⟨hstep, hc_nonneg, ?_⟩

  intro n hn

  rcases hgeom n hn with
    ⟨hr, hs⟩

  have hnNat :
      0 < n := by
    omega

  have hnReal :
      0 < (n : ℝ) := by
    exact_mod_cast hnNat

  have hD :
      0 < step * (n : ℝ) := by
    exact
      mul_pos
        hstep
        hnReal

  have h :=
    phiD_omitted_term_majorized
      hϱ
      h0
      h1
      hw
      hwL
      hD
      hr
      hs

  simpa [mul_pow] using h

end HurtadoZeta23
