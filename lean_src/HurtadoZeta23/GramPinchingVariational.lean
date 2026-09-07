import HurtadoZeta23.GramPinchingPositivePart
import Zeta23.LinAlg.HermitianPosPart
import Zeta23.LinAlg.RankTrace
import Mathlib.Tactic

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

universe u

namespace HurtadoZeta23

/-!
# Variational proof of two-block spectral Gram pinching

This file deliberately exports only the route actually consumed downstream.
The old experimental module contained several duplicated interfaces and stale
API experiments.  Here the argument is organized as follows.

* identify the spectral energy above `2` with the Frobenius energy of the
  positive part of `M - 2I`;
* prove the variational characterization of the Hermitian positive part;
* use the Boolean pinching as an orthogonal Frobenius projection;
* deduce the positive-part drop bound;
* feed it to `spectralGramPinching_bool_of_positivePartDrop`.

No zeta-function or asymptotic input occurs in this file.
-/

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ## Elementary pinching algebra -/

/-- Off-block component complementary to the Boolean pinch. -/
def offBlockPart (label : ι → Bool) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if label i = label j then 0 else M i j

theorem partitionPinch_add_offBlock
    (label : ι → Bool) (M : Matrix ι ι ℂ) :
    partitionPinch label M + offBlockPart label M = M := by
  ext i j
  by_cases h : label i = label j
  · simp [partitionPinch, offBlockPart, h]
  · simp [partitionPinch, offBlockPart, h]

theorem partitionPinch_isHermitian
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) :
    (partitionPinch label M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change
    star (if label j = label i then M j i else 0) =
      (if label i = label j then M i j else 0)
  by_cases h : label i = label j
  · have h' : label j = label i := h.symm
    rw [if_pos h', if_pos h]
    exact hM.apply i j
  · have h' : label j ≠ label i := by
      intro hj
      exact h hj.symm
    rw [if_neg h', if_neg h]
    exact map_zero (starRingEnd ℂ)

theorem offBlockPart_isHermitian
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) :
    (offBlockPart label M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change
    star (if label j = label i then 0 else M j i) =
      (if label i = label j then 0 else M i j)
  by_cases h : label i = label j
  · have h' : label j = label i := h.symm
    rw [if_pos h', if_pos h]
    exact map_zero (starRingEnd ℂ)
  · have h' : label j ≠ label i := by
      intro hj
      exact h hj.symm
    rw [if_neg h', if_neg h]
    exact hM.apply i j

/-- Pinching preserves PSD, via the already-compiled midpoint representation. -/
theorem partitionPinch_posSemidef
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) :
    (partitionPinch label M).PosSemidef := by
  rw [partitionPinch_bool_eq_midpoint_signConjugate]
  exact midpoint_posSemidef hM (signConjugate_posSemidef label M hM)

/-- Pinching fixes scalar diagonal shifts. -/
theorem partitionPinch_sub_smul_one
    (label : ι → Bool) (M : Matrix ι ι ℂ) (c : ℂ) :
    partitionPinch label (M - c • (1 : Matrix ι ι ℂ)) =
      partitionPinch label M - c • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases h : label i = label j
  · simp [partitionPinch, h]
  · have hij : i ≠ j := by
      intro hij
      subst j
      exact h rfl
    simp [partitionPinch, h, hij]

/-- Removing a scalar diagonal does not change the off-block component. -/
theorem offBlockPart_sub_smul_one
    (label : ι → Bool) (M : Matrix ι ι ℂ) (c : ℂ) :
    offBlockPart label (M - c • (1 : Matrix ι ι ℂ)) =
      offBlockPart label M := by
  ext i j
  by_cases h : label i = label j
  · simp [offBlockPart, h]
  · have hij : i ≠ j := by
      intro hij
      subst j
      exact h rfl
    simp [offBlockPart, h, hij]

/-- A block matrix times an off-block matrix has zero trace. -/
theorem trace_partitionPinch_mul_offBlock_eq_zero
    (label : ι → Bool) (A B : Matrix ι ι ℂ) :
    ((partitionPinch label A) * offBlockPart label B).trace = 0 := by
  classical
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro i hi
  change (partitionPinch label A * offBlockPart label B) i i = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases h : label i = label j
  · have h' : label j = label i := h.symm
    change
      (if label i = label j then A i j else 0) *
          (if label j = label i then 0 else B j i) = 0
    rw [if_pos h, if_pos h']
    exact mul_zero _
  · have h' : label j ≠ label i := by
      intro hj'
      exact h hj'.symm
    change
      (if label i = label j then A i j else 0) *
          (if label j = label i then 0 else B j i) = 0
    rw [if_neg h, if_neg h']
    exact zero_mul _

/-- The reverse cross trace also vanishes. -/
theorem trace_offBlock_mul_partitionPinch_eq_zero
    (label : ι → Bool) (A B : Matrix ι ι ℂ) :
    (offBlockPart label A * partitionPinch label B).trace = 0 := by
  classical
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro i hi
  change (offBlockPart label A * partitionPinch label B) i i = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases h : label i = label j
  · have h' : label j = label i := h.symm
    change
      (if label i = label j then 0 else A i j) *
          (if label j = label i then B j i else 0) = 0
    rw [if_pos h, if_pos h']
    exact zero_mul _
  · have h' : label j ≠ label i := by
      intro hj'
      exact h hj'.symm
    change
      (if label i = label j then 0 else A i j) *
          (if label j = label i then B j i else 0) = 0
    rw [if_neg h, if_neg h']
    exact mul_zero _

/-- Real trace pairing splits into block and off-block pieces. -/
theorem re_trace_mul_pinch_decomposition
    (label : ι → Bool) (A B : Matrix ι ι ℂ) :
    RCLike.re (A * B).trace =
      RCLike.re ((partitionPinch label A) *
        (partitionPinch label B)).trace +
      RCLike.re ((offBlockPart label A) *
        (offBlockPart label B)).trace := by
  calc
    RCLike.re (A * B).trace =
        RCLike.re
          (((partitionPinch label A + offBlockPart label A) *
            (partitionPinch label B + offBlockPart label B))).trace := by
          rw [partitionPinch_add_offBlock, partitionPinch_add_offBlock]
    _ =
        RCLike.re ((partitionPinch label A) *
          (partitionPinch label B)).trace +
        RCLike.re ((offBlockPart label A) *
          (offBlockPart label B)).trace := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
            Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
            map_add, map_add, map_add,
            trace_partitionPinch_mul_offBlock_eq_zero,
            trace_offBlock_mul_partitionPinch_eq_zero]
          simp

/-- Frobenius Pythagoras for Boolean pinching. -/
theorem frobSq_pinch_add_offBlock
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) :
    RHLinalg.frobSq M =
      RHLinalg.frobSq (partitionPinch label M) +
      RHLinalg.frobSq (offBlockPart label M) := by
  have hP := partitionPinch_isHermitian label M hM
  have hO := offBlockPart_isHermitian label M hM
  have hadd := RHLinalg.frobSq_add_hermitian hP hO
  have hcross :
      RCLike.re
        ((partitionPinch label M) * (offBlockPart label M)).trace = 0 := by
    rw [trace_partitionPinch_mul_offBlock_eq_zero]
    simp
  calc
    RHLinalg.frobSq M =
        RHLinalg.frobSq
          (partitionPinch label M + offBlockPart label M) := by
            rw [partitionPinch_add_offBlock]
    _ =
        RHLinalg.frobSq (partitionPinch label M) +
          RHLinalg.frobSq (offBlockPart label M) := by
            rw [hadd, hcross]
            ring

/-! ## Variational characterization of the positive part -/

theorem frobSq_nonneg_of_isHermitian
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    0 ≤ RHLinalg.frobSq M := by
  rw [RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hM]
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem frobSq_neg (M : Matrix ι ι ℂ) :
    RHLinalg.frobSq (-M) = RHLinalg.frobSq M := by
  unfold RHLinalg.frobSq
  simp

/-- Any PSD orthogonal decomposition `X = P - N` gives the universal
quadratic upper bound with maximizer candidate `P`. -/
theorem variational_upper_of_psd_decomposition
    (X P N Y : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hdec : P - N = X)
    (hY : Y.PosSemidef) :
    2 * RCLike.re (X * Y).trace - RHLinalg.frobSq Y
      ≤ RHLinalg.frobSq P := by
  have hneg : 0 ≤ RCLike.re (N * Y).trace :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hN hY
  have hdiffH : (P - Y).IsHermitian :=
    hP.isHermitian.sub hY.isHermitian
  have hnon : 0 ≤ RHLinalg.frobSq (P - Y) :=
    frobSq_nonneg_of_isHermitian (P - Y) hdiffH
  have hadd :=
    RHLinalg.frobSq_add_hermitian
      hP.isHermitian hY.isHermitian.neg
  have htrneg :
      RCLike.re (P * (-Y)).trace =
        - RCLike.re (P * Y).trace := by
    simp
  have hexpand :
      RHLinalg.frobSq (P - Y) =
        RHLinalg.frobSq P
          - 2 * RCLike.re (P * Y).trace
          + RHLinalg.frobSq Y := by
    rw [sub_eq_add_neg, hadd, htrneg, frobSq_neg]
    ring
  have htrace :
      RCLike.re (X * Y).trace =
        RCLike.re (P * Y).trace - RCLike.re (N * Y).trace := by
    rw [← hdec, Matrix.sub_mul, Matrix.trace_sub, map_sub]
  rw [hexpand] at hnon
  rw [htrace]
  linarith

/-- In a PSD orthogonal decomposition `X=P-N`, the candidate `P` attains
the variational value. -/
theorem variational_exact_of_psd_decomposition
    (X P N : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hdec : P - N = X)
    (horth : N * P = 0) :
    2 * RCLike.re (X * P).trace - RHLinalg.frobSq P
      = RHLinalg.frobSq P := by
  have hPH : P.IsHermitian := hP.isHermitian
  have hfrob :
      RHLinalg.frobSq P = RCLike.re (P * P).trace := by
    unfold RHLinalg.frobSq
    rw [hPH.eq]
  have htrace :
      RCLike.re (X * P).trace = RCLike.re (P * P).trace := by
    rw [← hdec, Matrix.sub_mul, horth]
    simp
  rw [htrace, ← hfrob]
  ring

theorem positivePart_variational_upper
    (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian)
    (hY : Y.PosSemidef) :
    2 * RCLike.re (X * Y).trace - RHLinalg.frobSq Y
      ≤ RHLinalg.frobSq (RHLinalg.hermPosPart hX) := by
  let Xp := RHLinalg.hermPosPart hX
  let Xn := RHLinalg.hermNegPart hX
  have hP : Xp.PosSemidef := RHLinalg.hermPosPart_posSemidef hX
  have hN : Xn.PosSemidef := RHLinalg.hermNegPart_posSemidef hX
  have hdec : Xp - Xn = X :=
    RHLinalg.hermPosPart_sub_hermNegPart hX
  change
    2 * RCLike.re (X * Y).trace - RHLinalg.frobSq Y
      ≤ RHLinalg.frobSq Xp
  exact variational_upper_of_psd_decomposition X Xp Xn Y hP hN hdec hY

theorem positivePart_variational_exact
    (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) :
    let Xp := RHLinalg.hermPosPart hX
    2 * RCLike.re (X * Xp).trace - RHLinalg.frobSq Xp
      = RHLinalg.frobSq Xp := by
  let Xp := RHLinalg.hermPosPart hX
  let Xn := RHLinalg.hermNegPart hX
  have hP : Xp.PosSemidef := RHLinalg.hermPosPart_posSemidef hX
  have hN : Xn.PosSemidef := RHLinalg.hermNegPart_posSemidef hX
  have hdec : Xp - Xn = X :=
    RHLinalg.hermPosPart_sub_hermNegPart hX
  have horth : Xn * Xp = 0 :=
    RHLinalg.hermNegPart_mul_hermPosPart hX
  change
    2 * RCLike.re (X * Xp).trace - RHLinalg.frobSq Xp
      = RHLinalg.frobSq Xp
  exact variational_exact_of_psd_decomposition X Xp Xn hP hN hdec horth

/-- Energy uniqueness of the positive component in any PSD orthogonal
decomposition. -/
theorem positivePartEnergy_eq_of_psd_decomposition
    (X P N : Matrix ι ι ℂ)
    (hX : X.IsHermitian)
    (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hdec : P - N = X)
    (horth : N * P = 0) :
    RHLinalg.frobSq P =
      RHLinalg.frobSq (RHLinalg.hermPosPart hX) := by
  let Xp := RHLinalg.hermPosPart hX
  have hXp : Xp.PosSemidef := RHLinalg.hermPosPart_posSemidef hX
  have hPexact :=
    variational_exact_of_psd_decomposition X P N hP hN hdec horth
  have hPupper := positivePart_variational_upper X P hX hP
  have hPle : RHLinalg.frobSq P ≤ RHLinalg.frobSq Xp := by
    change RHLinalg.frobSq P ≤ RHLinalg.frobSq Xp
    rw [hPexact] at hPupper
    exact hPupper
  have hXpExact := positivePart_variational_exact X hX
  have hXpUpper :=
    variational_upper_of_psd_decomposition X P N Xp hP hN hdec hXp
  have hXple : RHLinalg.frobSq Xp ≤ RHLinalg.frobSq P := by
    change RHLinalg.frobSq Xp ≤ RHLinalg.frobSq P
    rw [hXpExact] at hXpUpper
    exact hXpUpper
  exact le_antisymm hPle hXple

/-! ## Spectral realization of the breakpoint `2` -/

/-- `specMap` of a constant function is the scalar identity. -/
theorem specMap_const
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (c : ℝ) :
    RHLinalg.specMap hM (fun _ => c) =
      (c : ℂ) • (1 : Matrix ι ι ℂ) := by
  unfold RHLinalg.specMap
  rw [Unitary.conjStarAlgAut_apply]
  have hdiag :
      Matrix.diagonal (fun _ : ι => (c : ℂ)) =
        (c : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  change
    ((↑hM.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun _ : ι => (c : ℂ))) *
      star (↑hM.eigenvectorUnitary : Matrix ι ι ℂ) =
        (c : ℂ) • (1 : Matrix ι ι ℂ)
  rw [hdiag]
  simp

/-- Affine spectral calculus: `specMap (λ ↦ λ-c) = M-cI`. -/
theorem specMap_sub_const
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (c : ℝ) :
    RHLinalg.specMap hM (fun x => x - c) =
      M - (c : ℂ) • (1 : Matrix ι ι ℂ) := by
  have hfun :
      (fun x : ℝ => x - c) = id - (fun _ : ℝ => c) := by
    funext x
    rfl
  rw [hfun, RHLinalg.specMap_sub, RHLinalg.specMap_id,
    specMap_const M hM c]

/-- Spectral positive part above the breakpoint `2`, in the eigenbasis of M. -/
def aboveTwoMatrix
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) : Matrix ι ι ℂ :=
  RHLinalg.specMap hM.isHermitian aboveTwo

theorem aboveTwoMatrix_posSemidef
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    (aboveTwoMatrix M hM).PosSemidef := by
  unfold aboveTwoMatrix
  apply RHLinalg.specMap_posSemidef
  intro i
  exact le_max_right _ _

theorem frobSq_aboveTwoMatrix
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    RHLinalg.frobSq (aboveTwoMatrix M hM) =
      aboveTwoSpectralEnergy M hM := by
  unfold aboveTwoMatrix aboveTwoSpectralEnergy
  rw [RHLinalg.frobSq_specMap]
  exact
    RHLinalg.sum_eigenvalues_reindex
      hM.isHermitian (fun x => (aboveTwo x)^2)

def belowTwo (x : ℝ) : ℝ := max (2 - x) 0

theorem aboveTwo_sub_belowTwo (x : ℝ) :
    aboveTwo x - belowTwo x = x - 2 := by
  by_cases h : 2 ≤ x
  · have h1 : 0 ≤ x - 2 := by linarith
    have h2 : 2 - x ≤ 0 := by linarith
    simp [aboveTwo, belowTwo, max_eq_left h1, max_eq_right h2]
  · have h' : x ≤ 2 := le_of_not_ge h
    have h1 : x - 2 ≤ 0 := by linarith
    have h2 : 0 ≤ 2 - x := by linarith
    simp [aboveTwo, belowTwo, max_eq_right h1, max_eq_left h2]

def belowTwoMatrix
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) : Matrix ι ι ℂ :=
  RHLinalg.specMap hM.isHermitian belowTwo

theorem belowTwoMatrix_posSemidef
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    (belowTwoMatrix M hM).PosSemidef := by
  unfold belowTwoMatrix
  apply RHLinalg.specMap_posSemidef
  intro i
  exact le_max_right _ _

theorem belowTwoMatrix_mul_aboveTwoMatrix
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    belowTwoMatrix M hM * aboveTwoMatrix M hM = 0 := by
  unfold belowTwoMatrix aboveTwoMatrix
  rw [← RHLinalg.specMap_mul]
  have hzero : (belowTwo * aboveTwo : ℝ → ℝ) = 0 := by
    funext x
    by_cases h : 2 ≤ x
    · have h1 : 0 ≤ x - 2 := by linarith
      have h2 : 2 - x ≤ 0 := by linarith
      simp [aboveTwo, belowTwo, h1, h2]
    · have h' : x ≤ 2 := le_of_not_ge h
      have h1 : x - 2 ≤ 0 := by linarith
      have h2 : 0 ≤ 2 - x := by linarith
      simp [aboveTwo, belowTwo, h1, h2]
  rw [hzero, RHLinalg.specMap_zero]

theorem shiftAtTwo_isHermitian
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    (M - (2 : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  have hs :=
    RHLinalg.specMap_isHermitian hM.isHermitian (fun x => x - 2)
  have heq :
      RHLinalg.specMap hM.isHermitian (fun x => x - 2) =
        M - (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
    convert specMap_sub_const M hM.isHermitian 2 using 1 <;> norm_num
  rw [heq] at hs
  exact hs

theorem shiftAtOne_isHermitian
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    (M - (1 : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  have hs :=
    RHLinalg.specMap_isHermitian hM.isHermitian (fun x => x - 1)
  have heq :
      RHLinalg.specMap hM.isHermitian (fun x => x - 1) =
        M - (1 : ℂ) • (1 : Matrix ι ι ℂ) := by
    convert specMap_sub_const M hM.isHermitian 1 using 1 <;> norm_num
  rw [heq] at hs
  exact hs

/-- The two spectral pieces form the PSD orthogonal decomposition of `M-2I`. -/
theorem aboveBelowTwo_decomposition
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    aboveTwoMatrix M hM - belowTwoMatrix M hM =
      M - (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
  unfold aboveTwoMatrix belowTwoMatrix
  rw [← RHLinalg.specMap_sub]
  have hfun : (aboveTwo - belowTwo : ℝ → ℝ) =
      fun x => x - 2 := by
    funext x
    exact aboveTwo_sub_belowTwo x
  rw [hfun]
  convert specMap_sub_const M hM.isHermitian 2 using 1 <;> norm_num

noncomputable def shiftedPositivePartEnergy
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) : ℝ :=
  RHLinalg.frobSq
    (RHLinalg.hermPosPart (shiftAtTwo_isHermitian M hM))

theorem shiftedPositivePartEnergy_eq_aboveTwoSpectralEnergy
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    shiftedPositivePartEnergy M hM =
      aboveTwoSpectralEnergy M hM := by
  let X := M - (2 : ℂ) • (1 : Matrix ι ι ℂ)
  let hX : X.IsHermitian := shiftAtTwo_isHermitian M hM
  have hP := aboveTwoMatrix_posSemidef M hM
  have hN := belowTwoMatrix_posSemidef M hM
  have hdec :
      aboveTwoMatrix M hM - belowTwoMatrix M hM = X := by
    simpa [X] using aboveBelowTwo_decomposition M hM
  have horth :
      belowTwoMatrix M hM * aboveTwoMatrix M hM = 0 :=
    belowTwoMatrix_mul_aboveTwoMatrix M hM
  have henergy :=
    positivePartEnergy_eq_of_psd_decomposition
      X (aboveTwoMatrix M hM) (belowTwoMatrix M hM)
      hX hP hN hdec horth
  unfold shiftedPositivePartEnergy
  change
    RHLinalg.frobSq (RHLinalg.hermPosPart hX) =
      aboveTwoSpectralEnergy M hM
  calc
    RHLinalg.frobSq (RHLinalg.hermPosPart hX) =
        RHLinalg.frobSq (aboveTwoMatrix M hM) := henergy.symm
    _ = aboveTwoSpectralEnergy M hM :=
      frobSq_aboveTwoMatrix M hM

/-- The centered spectral energy is exactly `‖M-I‖_F²`. -/
theorem centeredSpectralEnergy_eq_frobSq_shiftOne
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    centeredSpectralEnergy M hM =
      RHLinalg.frobSq
        (M - (1 : ℂ) • (1 : Matrix ι ι ℂ)) := by
  unfold centeredSpectralEnergy
  have hspec :
      RHLinalg.specMap hM.isHermitian (fun x => x - 1) =
        M - (1 : ℂ) • (1 : Matrix ι ι ℂ) := by
    convert specMap_sub_const M hM.isHermitian 1 using 1 <;> norm_num
  rw [← hspec]
  rw [RHLinalg.frobSq_specMap]
  exact
    (RHLinalg.sum_eigenvalues_reindex
      hM.isHermitian (fun x => (x - 1)^2)).symm

/-! ## The positive-part drop under pinching -/

/-- Completion of squares in an off-block Hermitian component. -/
theorem offBlock_completion
    (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    2 * RCLike.re (A * B).trace - RHLinalg.frobSq B
      ≤ RHLinalg.frobSq A := by
  have hdiff : (A - B).IsHermitian := hA.sub hB
  have hnon : 0 ≤ RHLinalg.frobSq (A - B) :=
    frobSq_nonneg_of_isHermitian (A - B) hdiff
  have hadd :=
    RHLinalg.frobSq_add_hermitian hA hB.neg
  have htrneg :
      RCLike.re (A * (-B)).trace =
        - RCLike.re (A * B).trace := by
    simp
  have hexpand :
      RHLinalg.frobSq (A - B) =
        RHLinalg.frobSq A
          - 2 * RCLike.re (A * B).trace
          + RHLinalg.frobSq B := by
    rw [sub_eq_add_neg, hadd, htrneg, frobSq_neg]
    ring
  rw [hexpand] at hnon
  linarith

/-- Variational contraction of the positive-part energy under Boolean pinching. -/
theorem shiftedPositivePartEnergy_drop_le_offBlock
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef)
    (hEM : (partitionPinch label M).PosSemidef) :
    shiftedPositivePartEnergy M hM -
        shiftedPositivePartEnergy (partitionPinch label M) hEM
      ≤ RHLinalg.frobSq (offBlockPart label M) := by
  let EM := partitionPinch label M
  let X := M - (2 : ℂ) • (1 : Matrix ι ι ℂ)
  let hX : X.IsHermitian := shiftAtTwo_isHermitian M hM
  let EX := EM - (2 : ℂ) • (1 : Matrix ι ι ℂ)
  let hEX : EX.IsHermitian := shiftAtTwo_isHermitian EM hEM
  let P := RHLinalg.hermPosPart hX
  let Q := RHLinalg.hermPosPart hEX
  let EP := partitionPinch label P
  let OP := offBlockPart label P
  let OX := offBlockPart label X

  have hP : P.PosSemidef := RHLinalg.hermPosPart_posSemidef hX
  have hEP : EP.PosSemidef := by
    exact partitionPinch_posSemidef label P hP
  have hPH : P.IsHermitian := hP.isHermitian
  have hEPH : EP.IsHermitian := hEP.isHermitian
  have hOPH : OP.IsHermitian := by
    exact offBlockPart_isHermitian label P hPH
  have hOXH : OX.IsHermitian := by
    exact offBlockPart_isHermitian label X hX

  have hEXeq : partitionPinch label X = EX := by
    simpa [X, EX, EM] using
      partitionPinch_sub_smul_one label M (2 : ℂ)

  have hvarEX :
      2 * RCLike.re (EX * EP).trace - RHLinalg.frobSq EP
        ≤ RHLinalg.frobSq Q := by
    exact positivePart_variational_upper EX EP hEX hEP

  have hexactX :
      2 * RCLike.re (X * P).trace - RHLinalg.frobSq P
        = RHLinalg.frobSq P := by
    exact positivePart_variational_exact X hX

  have hsplit0 := re_trace_mul_pinch_decomposition label X P
  have hsplit :
      RCLike.re (X * P).trace =
        RCLike.re (EX * EP).trace +
        RCLike.re (OX * OP).trace := by
    rw [hEXeq] at hsplit0
    simpa [EP, OP, OX] using hsplit0

  have hpyth0 := frobSq_pinch_add_offBlock label P hPH
  have hpyth :
      RHLinalg.frobSq P =
        RHLinalg.frobSq EP + RHLinalg.frobSq OP := by
    simpa [EP, OP] using hpyth0

  have hcomp :
      2 * RCLike.re (OX * OP).trace - RHLinalg.frobSq OP
        ≤ RHLinalg.frobSq OX :=
    offBlock_completion OX OP hOXH hOPH

  have hmain :
      RHLinalg.frobSq P - RHLinalg.frobSq Q
        ≤ RHLinalg.frobSq OX := by
    linarith [hexactX, hsplit, hpyth, hvarEX, hcomp]

  have hOXeq : OX = offBlockPart label M := by
    simpa [OX, X] using
      offBlockPart_sub_smul_one label M (2 : ℂ)

  unfold shiftedPositivePartEnergy
  change
    RHLinalg.frobSq P - RHLinalg.frobSq Q
      ≤ RHLinalg.frobSq (offBlockPart label M)
  rw [← hOXeq]
  exact hmain

/-- The centered quadratic drop is exactly the off-block Frobenius energy. -/
theorem centeredSpectralEnergy_drop_eq_offBlock
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef)
    (hEM : (partitionPinch label M).PosSemidef) :
    centeredSpectralEnergy M hM -
        centeredSpectralEnergy (partitionPinch label M) hEM
      = RHLinalg.frobSq (offBlockPart label M) := by
  let EM := partitionPinch label M
  let X := M - (1 : ℂ) • (1 : Matrix ι ι ℂ)
  let hX : X.IsHermitian := shiftAtOne_isHermitian M hM

  have hpyth := frobSq_pinch_add_offBlock label X hX
  have hEX :
      partitionPinch label X =
        EM - (1 : ℂ) • (1 : Matrix ι ι ℂ) := by
    simpa [X, EM] using
      partitionPinch_sub_smul_one label M (1 : ℂ)
  have hOX :
      offBlockPart label X = offBlockPart label M := by
    simpa [X] using
      offBlockPart_sub_smul_one label M (1 : ℂ)

  rw [hEX, hOX] at hpyth
  rw [centeredSpectralEnergy_eq_frobSq_shiftOne M hM,
      centeredSpectralEnergy_eq_frobSq_shiftOne EM hEM]
  linarith

/-- The isolated positive-part drop hypothesis from `GramPinchingPositivePart`
is now proved. -/
theorem pinchingPositivePartDropBound_proved :
    PinchingPositivePartDropBound.{u} := by
  intro κ _ _ M hM label
  dsimp
  intro hEM
  have hplus :=
    shiftedPositivePartEnergy_drop_le_offBlock label M hM hEM
  have hbridgeM :=
    shiftedPositivePartEnergy_eq_aboveTwoSpectralEnergy M hM
  have hbridgeE :=
    shiftedPositivePartEnergy_eq_aboveTwoSpectralEnergy
      (partitionPinch label M) hEM
  have hcenter :=
    centeredSpectralEnergy_drop_eq_offBlock label M hM hEM
  calc
    aboveTwoSpectralEnergy M hM -
        aboveTwoSpectralEnergy (partitionPinch label M) hEM
      =
        shiftedPositivePartEnergy M hM -
          shiftedPositivePartEnergy (partitionPinch label M) hEM := by
            rw [hbridgeM, hbridgeE]
    _ ≤ RHLinalg.frobSq (offBlockPart label M) := hplus
    _ =
        centeredSpectralEnergy M hM -
          centeredSpectralEnergy (partitionPinch label M) hEM := hcenter.symm

/-- Direct inequality with an explicit PSD witness for the pinched matrix. -/
theorem spectralGramPinching_bool_ineq
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef)
    (hP : (partitionPinch label M).PosSemidef) :
    gramSpectralDefect (partitionPinch label M) hP
      ≤ gramSpectralDefect M hM := by
  exact spectralGramPinching_bool_of_positivePartDrop
    pinchingPositivePartDropBound_proved M hM label hP

/-- The exact packaged theorem consumed by `GramPinchingBlockDiagonal`. -/
theorem spectralGramPinching_bool_proved
    (label : ι → Bool) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) :
    SpectralGramPinching M hM label := by
  let hP : (partitionPinch label M).PosSemidef :=
    partitionPinch_posSemidef label M hM
  exact ⟨hP, spectralGramPinching_bool_ineq label M hM hP⟩

end HurtadoZeta23
