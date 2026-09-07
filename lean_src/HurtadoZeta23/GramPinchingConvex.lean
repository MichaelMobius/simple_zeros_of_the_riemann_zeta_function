import HurtadoZeta23.GramPinching
import HurtadoZeta23.RootMultisetGramBridge
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped ComplexOrder

universe u

namespace HurtadoZeta23

/-!
# Convex core for Gram-defect pinching

This file advances the corrected partition-pinching argument of v5.1.

The scalar function `psi` is convex.  We prove the midpoint inequality
explicitly, including the two mixed cases crossing the breakpoint `2`.

At matrix level we isolate one genuinely spectral fact:

  `gramSpectralDefect ((A+B)/2) ≤ (D(A)+D(B))/2`.

Once this midpoint spectral convexity and invariance under diagonal-sign
conjugation are available, the two-block pinching inequality follows
immediately from the exact identity proved in `GramPinching.lean`.

This is intentionally narrower than claiming a general spectral-convexity API
already exists in Mathlib; the scalar convexity is kernel-level in this file,
while the spectral lifting remains explicit.
-/

/-- Midpoint convexity of the paper's scalar defect `psi` on all of `ℝ`. -/
theorem psi_midpoint_le (x y : ℝ) :
    psi ((x + y) / 2) ≤ (psi x + psi y) / 2 := by
  by_cases hx : x ≤ 2
  · by_cases hy : y ≤ 2
    · have hm : (x + y) / 2 ≤ 2 := by linarith
      rw [psi_eq_sq hx, psi_eq_sq hy, psi_eq_sq hm]
      nlinarith [sq_nonneg (x - y)]
    · have hy2 : 2 < y := lt_of_not_ge hy
      by_cases hm : (x + y) / 2 ≤ 2
      · rw [psi_eq_sq hx, psi_eq_linear hy2, psi_eq_sq hm]
        nlinarith [sq_nonneg (x - 2)]
      · have hm2 : 2 < (x + y) / 2 := lt_of_not_ge hm
        rw [psi_eq_sq hx, psi_eq_linear hy2, psi_eq_linear hm2]
        nlinarith [sq_nonneg (x - 2)]
  · have hx2 : 2 < x := lt_of_not_ge hx
    by_cases hy : y ≤ 2
    · by_cases hm : (x + y) / 2 ≤ 2
      · rw [psi_eq_linear hx2, psi_eq_sq hy, psi_eq_sq hm]
        nlinarith [sq_nonneg (y - 2)]
      · have hm2 : 2 < (x + y) / 2 := lt_of_not_ge hm
        rw [psi_eq_linear hx2, psi_eq_sq hy, psi_eq_linear hm2]
        nlinarith [sq_nonneg (y - 2)]
    · have hy2 : 2 < y := lt_of_not_ge hy
      have hm2 : 2 < (x + y) / 2 := by linarith
      rw [psi_eq_linear hx2, psi_eq_linear hy2, psi_eq_linear hm2]
      ring_nf
      exact le_rfl

/-- The exact spectral midpoint-convexity statement still needed to lift the
proved scalar convexity of `psi` from eigenvalues to Hermitian PSD matrices. -/
def GramDefectMidpointConvexity : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (A B : Matrix ι ι ℂ)
      (hA : A.PosSemidef) (hB : B.PosSemidef),
    ∀ hMid : (((2 : ℂ)⁻¹) • (A + B)).PosSemidef,
      gramSpectralDefect (((2 : ℂ)⁻¹) • (A + B)) hMid
        ≤ (gramSpectralDefect A hA + gramSpectralDefect B hB) / 2

/-- Invariance of the Gram spectral defect under the diagonal ±1 conjugation
used by a two-block pinching.  This is a similarity-invariance fact: the two
matrices have the same characteristic polynomial/eigenvalue multiset. -/
def SignConjugateDefectInvariance : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (label : ι → Bool) (M : Matrix ι ι ℂ) (hM : M.PosSemidef),
    ∃ hU : (signConjugate label M).PosSemidef,
      gramSpectralDefect (signConjugate label M) hU =
        gramSpectralDefect M hM

/-- PSD preservation for the midpoint, once both endpoints are PSD. -/
lemma midpoint_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (((2 : ℂ)⁻¹) • (A + B)).PosSemidef := by
  have hsum : (A + B).PosSemidef := hA.add hB
  have hhalfR : (0 : ℝ) ≤ (1 / 2 : ℝ) := by
    norm_num
  have hcoef : ((2 : ℂ)⁻¹) = (((1 / 2 : ℝ) : ℂ)) := by
    norm_num
  have hhalf : (0 : ℂ) ≤ ((2 : ℂ)⁻¹) := by
    rw [hcoef]
    exact Complex.zero_le_real.mpr hhalfR
  exact hsum.smul hhalf

/-- **Two-block Gram-defect pinching**, reduced to one spectral convexity fact
plus similarity invariance.  The structural identity
`partitionPinch_bool_eq_midpoint_signConjugate` is already proved in v5.1. -/
theorem spectralGramPinching_bool_of_convexity
    (hconv : GramDefectMidpointConvexity.{u})
    (hinv : SignConjugateDefectInvariance.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → Bool) :
    SpectralGramPinching M hM label := by
  rcases hinv label M hM with ⟨hU, hDU⟩
  let Mid : Matrix ι ι ℂ := (2 : ℂ)⁻¹ • (M + signConjugate label M)
  have hMid : Mid.PosSemidef := by
    dsimp [Mid]
    exact midpoint_posSemidef hM hU
  have hEq :
      partitionPinch label M = Mid := by
    simpa [Mid] using
      partitionPinch_bool_eq_midpoint_signConjugate label M
  have hPM : (partitionPinch label M).PosSemidef := by
    rw [hEq]
    exact hMid
  refine ⟨hPM, ?_⟩
  have hc := hconv M (signConjugate label M) hM hU hMid
  rw [hDU] at hc
  have hcMid :
      gramSpectralDefect Mid hMid ≤ gramSpectralDefect M hM := by
    simpa [Mid] using hc
  have hDefEq :
      gramSpectralDefect (partitionPinch label M) hPM =
        gramSpectralDefect Mid hMid := by
    exact gramSpectralDefect_eq_of_matrix_eq hPM hMid hEq
  exact hDefEq.trans_le hcMid

/-- Once direct-sum additivity is supplied, the corrected two-block partition
inequality is now automatic from the single spectral midpoint-convexity fact
and sign-conjugation invariance. -/
theorem gramDefectPinching_bool_of_convexity
    (hconv : GramDefectMidpointConvexity.{u})
    (hinv : SignConjugateDefectInvariance.{u})
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) (label : ι → Bool)
    (hadd : BlockDiagonalDefectAdditivity M hM label) :
    GramDefectPinchingPartition M hM label := by
  exact gramDefectPinchingPartition_of_standard_facts M hM label
    (spectralGramPinching_bool_of_convexity hconv hinv M hM label) hadd

end HurtadoZeta23
