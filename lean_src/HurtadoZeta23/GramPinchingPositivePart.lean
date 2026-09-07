import HurtadoZeta23.GramPinchingInvariant
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder

universe u

namespace HurtadoZeta23

/-!
# Positive-part reduction for spectral Gram pinching

For the paper's scalar defect

  psi(x) = (x-1)^2                  for x ≤ 2
         = 2x-3                     for x > 2,

we use the exact identity

  psi(x) = (x-1)^2 - (max (x-2) 0)^2.

Thus spectral pinching is reduced to comparing the drop of two explicit
spectral energies.  This avoids assuming a general Jensen theorem for convex
spectral functions and isolates a narrower matrix inequality.
-/

/-- Positive part of `x - 2`. -/
def aboveTwo (x : ℝ) : ℝ := max (x - 2) 0

/-- Exact scalar decomposition of the stability defect. -/
theorem psi_eq_centered_sq_sub_aboveTwo_sq (x : ℝ) :
    psi x = (x - 1)^2 - (aboveTwo x)^2 := by
  by_cases hx : x ≤ 2
  · rw [psi_eq_sq hx]
    have h : x - 2 ≤ 0 := by linarith
    simp [aboveTwo, max_eq_right h]
  · have hx2 : 2 < x := lt_of_not_ge hx
    rw [psi_eq_linear hx2]
    have h : 0 ≤ x - 2 := by linarith
    rw [aboveTwo, max_eq_left h]
    ring

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Spectral quadratic energy around the identity. -/
def centeredSpectralEnergy
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) : ℝ :=
  ∑ i, (hM.isHermitian.eigenvalues₀ i - 1)^2

/-- Spectral energy carried by eigenvalues above the breakpoint `2`. -/
def aboveTwoSpectralEnergy
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) : ℝ :=
  ∑ i, (aboveTwo (hM.isHermitian.eigenvalues₀ i))^2

/-- Exact matrix-level decomposition, obtained term-by-term from the scalar
identity.  No matrix convexity is used here. -/
theorem gramSpectralDefect_eq_centered_sub_aboveTwo
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    gramSpectralDefect M hM =
      centeredSpectralEnergy M hM - aboveTwoSpectralEnergy M hM := by
  unfold gramSpectralDefect centeredSpectralEnergy aboveTwoSpectralEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact psi_eq_centered_sq_sub_aboveTwo_sq _

/-- The precise quantitative statement sufficient for defect monotonicity:
the loss in the above-two energy is at most the loss in centered quadratic
energy. -/
def PinchingPositivePartDropBound : Prop :=
  ∀ {κ : Type u} [Fintype κ] [DecidableEq κ]
      (M : Matrix κ κ ℂ) (hM : M.PosSemidef) (label : κ → Bool),
    let P := partitionPinch label M
    ∀ hP : P.PosSemidef,
      aboveTwoSpectralEnergy M hM - aboveTwoSpectralEnergy P hP
        ≤ centeredSpectralEnergy M hM - centeredSpectralEnergy P hP

/-- The positive-part drop bound implies the two-block spectral pinching
inequality directly, using only the exact decomposition above. -/
theorem spectralGramPinching_bool_of_positivePartDrop
    (hdrop : PinchingPositivePartDropBound.{u})
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → Bool)
    (hP : (partitionPinch label M).PosSemidef) :
    gramSpectralDefect (partitionPinch label M) hP
      ≤ gramSpectralDefect M hM := by
  have hd := hdrop M hM label hP
  rw [gramSpectralDefect_eq_centered_sub_aboveTwo,
      gramSpectralDefect_eq_centered_sub_aboveTwo]
  linarith

/-- Hence the remaining global pinching frontier can be replaced by the
single quantitative drop bound above. -/
theorem spectralGramPinching_bool_of_positivePartDrop_packaged
    (hdrop : PinchingPositivePartDropBound.{u})
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → Bool) :
    SpectralGramPinching M hM label := by
  let hP : (partitionPinch label M).PosSemidef := by
    rw [partitionPinch_bool_eq_midpoint_signConjugate]
    exact midpoint_posSemidef hM (signConjugate_posSemidef label M hM)
  exact ⟨hP, spectralGramPinching_bool_of_positivePartDrop hdrop M hM label hP⟩

end HurtadoZeta23
