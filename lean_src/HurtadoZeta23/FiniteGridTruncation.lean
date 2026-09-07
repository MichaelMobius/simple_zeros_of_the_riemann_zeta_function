import HurtadoZeta23.PoissonGaborBridge
import HurtadoZeta23.WindowKernelLimit
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- The full-grid Gabor summand for the Montgomery--Taylor window. -/
def phiDGridSummand
    (ϱ : ℝ → ℝ)
    (lam L w T τ τ' : ℝ)
    (k : ℤ) : ℝ :=
  Zeta23.AdmWindow.vHatR
      (Zeta23.ThmD.phiD ϱ lam L w)
      (τ - (T + k * (2 * Real.pi / L))) *
    Zeta23.AdmWindow.vHatR
      (Zeta23.ThmD.phiD ϱ lam L w)
      (τ' - (T + k * (2 * Real.pi / L)))

/--
Zeta23's Poisson theorem supplies absolute summability of the full
critical lattice.
-/
theorem summable_phiD_full_grid
    {ϱ : ℝ → ℝ}
    {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    (T τ τ' : ℝ) :
    Summable
      (phiDGridSummand ϱ lam L w T τ τ') := by

  have hs :=
    hasSum_phiD_full_grid
      hϱ h0 h1 hw hwL T τ τ'

  change
    Summable
      (fun k : ℤ =>
        Zeta23.AdmWindow.vHatR
            (Zeta23.ThmD.phiD ϱ lam L w)
            (τ - (T + k * (2 * Real.pi / L))) *
          Zeta23.AdmWindow.vHatR
            (Zeta23.ThmD.phiD ϱ lam L w)
            (τ' - (T + k * (2 * Real.pi / L))))

  exact hs.summable

/--
A finite lattice truncation on an arbitrary finite set of indices.
-/
def finiteGridOverlap
    (ϱ : ℝ → ℝ)
    (lam L w T τ τ' : ℝ)
    (s : Finset ℤ) : ℝ :=
  ∑ k ∈ s,
    phiDGridSummand ϱ lam L w T τ τ' k

/--
Exact infinite-grid overlap from Poisson.
-/
def fullGridOverlap
    (ϱ : ℝ → ℝ)
    (lam L w τ τ' : ℝ) : ℝ :=
  L *
    Zeta23.AdmWindow.VPhiR
      (Zeta23.ThmD.phiD ϱ lam L w)
      (τ - τ')

/--
The finite-tail statement in the exact topology used by `HasSum`:
once a finite core is retained, all larger finite grids approximate
the Poisson overlap.

This is obtained directly from the `Tendsto` contained in `HasSum`.
No additional analytic assumption is introduced.
-/
theorem finite_grid_eventually_close
    {ϱ : ℝ → ℝ}
    {lam L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L)
    (T τ τ' eps : ℝ)
    (heps : 0 < eps) :
    ∃ s0 : Finset ℤ,
      ∀ s : Finset ℤ,
        s0 ⊆ s →
          |finiteGridOverlap ϱ lam L w T τ τ' s -
            fullGridOverlap ϱ lam L w τ τ'| < eps := by

  let f : ℤ → ℝ :=
    phiDGridSummand ϱ lam L w T τ τ'

  let a : ℝ :=
    fullGridOverlap ϱ lam L w τ τ'

  have hs : HasSum f a := by
    dsimp [f, a]

    unfold phiDGridSummand
    unfold fullGridOverlap

    exact
      hasSum_phiD_full_grid
        hϱ h0 h1 hw hwL T τ τ'

  have hball :
      Metric.ball a eps ∈ 𝓝 a := by
    exact Metric.ball_mem_nhds a heps

  have hev :
      {s : Finset ℤ |
        ∑ k ∈ s, f k ∈ Metric.ball a eps}
        ∈ atTop := by

    exact hs hball

  rcases mem_atTop_sets.mp hev with
    ⟨s0, hs0⟩

  refine ⟨s0, ?_⟩

  intro s hsub

  have hs_mem :
      s ∈
        {s : Finset ℤ |
          ∑ k ∈ s, f k ∈ Metric.ball a eps} := by

    exact hs0 s hsub

  have hdist :
      dist (∑ k ∈ s, f k) a < eps := by

    simpa [Metric.mem_ball] using hs_mem

  dsimp [f, a] at hdist

  simpa [
    finiteGridOverlap,
    fullGridOverlap,
    phiDGridSummand,
    Real.dist_eq
  ] using hdist

/--
What remains for Appendix IV is uniformity of the preceding truncation
on a compact normalized separation range and for the particular retained
finite lattice.

The definition makes that frontier explicit.
-/
def UniformFiniteGridTruncation
    (finiteOverlap fullOverlap : ℝ → ℝ → ℝ)
    (R eps : ℝ) : Prop :=
  ∀ x x',
    |x - x'| ≤ R →
      |finiteOverlap x x' - fullOverlap x x'| ≤ eps

/--
Once finite-grid truncation and the full-grid window limit are separately
controlled, the desired compact overlap estimate is their sum.
-/
theorem compact_overlap_from_two_errors
    {finite full limit : ℝ → ℝ → ℝ}
    {R tailErr windowErr : ℝ}
    (htail :
      UniformFiniteGridTruncation
        finite full R tailErr)
    (hwindow :
      ∀ x x',
        |x - x'| ≤ R →
          |full x x' - limit x x'| ≤ windowErr) :
    UniformFiniteGridTruncation
      finite limit R (tailErr + windowErr) := by

  intro x x' hx

  exact
    overlap_error_triangle
      (htail x x' hx)
      (hwindow x x' hx)

end HurtadoZeta23