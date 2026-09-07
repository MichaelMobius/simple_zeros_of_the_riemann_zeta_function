import HurtadoZeta23.V17AdjacentPair
import HurtadoZeta23.GramPinchingFinitePartition
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

section ProductPairs

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The fiber of `Prod.fst : β × Fin 2 → β` is canonically `Fin 2`. -/
def v17PairFiberEquiv (b : β) :
    {i : β × Fin 2 // i.1 = b} ≃ Fin 2 where
  toFun i := i.1.2
  invFun j := ⟨(b, j), rfl⟩
  left_inv i := by
    rcases i with ⟨⟨b', j⟩, hb⟩
    simp only at hb
    subst b'
    rfl
  right_inv j := rfl

/-- One two-point fiber of a unit-diagonal product partition has exactly twice
the squared norm of its off-diagonal entry as Gram defect. -/
theorem v17_product_fiber_defect
    (M : Matrix (β × Fin 2) (β × Fin 2) ℂ)
    (hM : M.PosSemidef)
    (hdiag : ∀ i, M i i = 1)
    (b : β) :
    gramSpectralDefect
        (finitePartitionBlock (fun i : β × Fin 2 => i.1) M b)
        (finitePartitionBlock_posSemidef
          (fun i : β × Fin 2 => i.1) M hM b)
      = 2 * ‖M (b, 0) (b, 1)‖ ^ 2 := by
  let part : β × Fin 2 → β := fun i => i.1
  let B := finitePartitionBlock part M b
  let hB : B.PosSemidef := finitePartitionBlock_posSemidef part M hM b
  let e := v17PairFiberEquiv b
  let B2 := Matrix.reindex e e B
  let hB2 : B2.PosSemidef := posSemidef_reindex e B hB
  have h00 : B2 0 0 = 1 := by
    simp [B2, B, e, part, v17PairFiberEquiv, finitePartitionBlock,
      Matrix.reindex_apply, hdiag]
  have h11 : B2 1 1 = 1 := by
    simp [B2, B, e, part, v17PairFiberEquiv, finitePartitionBlock,
      Matrix.reindex_apply, hdiag]
  have h01 : B2 0 1 = M (b, 0) (b, 1) := by
    simp [B2, B, e, part, v17PairFiberEquiv, finitePartitionBlock,
      Matrix.reindex_apply]
  have hdef2 := v17_fin2_gram_defect_eq_two_offdiag B2 hB2 h00 h11
  have hre := gramSpectralDefect_reindex e B hB
  have hleft :
      gramSpectralDefect B hB = 2 * ‖M (b, 0) (b, 1)‖ ^ 2 := by
    calc
      gramSpectralDefect B hB
          = gramSpectralDefect B2 hB2 := hre.symm
      _ = 2 * ‖B2 0 1‖ ^ 2 := hdef2
      _ = 2 * ‖M (b, 0) (b, 1)‖ ^ 2 := by rw [h01]
  simpa [B, hB, part] using hleft

/-- Finite-partition pinching specialised to a disjoint family of unit-diagonal
two-point fibers. -/
theorem v17_product_pair_pinching
    (M : Matrix (β × Fin 2) (β × Fin 2) ℂ)
    (hM : M.PosSemidef)
    (hdiag : ∀ i, M i i = 1) :
    (∑ b : β, 2 * ‖M (b, 0) (b, 1)‖ ^ 2)
      ≤ gramSpectralDefect M hM := by
  let part : β × Fin 2 → β := fun i => i.1
  have hp := finitePartitionGramPinching_proved part M hM
  calc
    (∑ b : β, 2 * ‖M (b, 0) (b, 1)‖ ^ 2)
        = ∑ b : β,
            gramSpectralDefect
              (finitePartitionBlock part M b)
              (finitePartitionBlock_posSemidef part M hM b) := by
            apply Finset.sum_congr rfl
            intro b hb
            symm
            simpa [part] using v17_product_fiber_defect M hM hdiag b
    _ ≤ gramSpectralDefect M hM := hp

/-- Robust finite-Gram lower bound for one product fiber.  Exact unit diagonal
is replaced by the natural column-norm condition `Re M_ii ≤ 1`. -/
theorem v17_product_fiber_defect_ge_of_diag_re_le_one
    (M : Matrix (β × Fin 2) (β × Fin 2) ℂ)
    (hM : M.PosSemidef)
    (hdiag : ∀ i, (M i i).re ≤ 1)
    (b : β) :
    2 * ‖M (b, 0) (b, 1)‖ ^ 2 ≤
      gramSpectralDefect
        (finitePartitionBlock (fun i : β × Fin 2 => i.1) M b)
        (finitePartitionBlock_posSemidef
          (fun i : β × Fin 2 => i.1) M hM b) := by
  let part : β × Fin 2 → β := fun i => i.1
  let B := finitePartitionBlock part M b
  let hB : B.PosSemidef := finitePartitionBlock_posSemidef part M hM b
  let e := v17PairFiberEquiv b
  let B2 := Matrix.reindex e e B
  let hB2 : B2.PosSemidef := posSemidef_reindex e B hB
  have htrace : RHLinalg.rtrace B2 ≤ 2 := by
    unfold RHLinalg.rtrace Matrix.trace
    simp [B2, B, e, part, v17PairFiberEquiv, finitePartitionBlock,
      Matrix.reindex_apply]
    linarith [hdiag (b, (0 : Fin 2)), hdiag (b, (1 : Fin 2))]
  have h01 : B2 0 1 = M (b, 0) (b, 1) := by
    simp [B2, B, e, part, v17PairFiberEquiv, finitePartitionBlock,
      Matrix.reindex_apply]
  have hdef2 := v17_fin2_gram_defect_ge_two_offdiag_of_rtrace_le B2 hB2 htrace
  have hre := gramSpectralDefect_reindex e B hB
  have hleft :
      2 * ‖M (b, 0) (b, 1)‖ ^ 2 ≤ gramSpectralDefect B hB := by
    rw [← h01]
    calc
      2 * ‖B2 0 1‖ ^ 2 ≤ gramSpectralDefect B2 hB2 := hdef2
      _ = gramSpectralDefect B hB := hre
  simpa [B, hB, part] using hleft

/-- Robust pair-family pinching for actual finite Gram matrices.  It consumes
only PSD and `Re M_ii ≤ 1`, exactly the information supplied by the synthesis
column norm bound. -/
theorem v17_product_pair_pinching_of_diag_re_le_one
    (M : Matrix (β × Fin 2) (β × Fin 2) ℂ)
    (hM : M.PosSemidef)
    (hdiag : ∀ i, (M i i).re ≤ 1) :
    (∑ b : β, 2 * ‖M (b, 0) (b, 1)‖ ^ 2)
      ≤ gramSpectralDefect M hM := by
  let part : β × Fin 2 → β := fun i => i.1
  have hp := finitePartitionGramPinching_proved part M hM
  have hfiber :
      ∀ b : β,
        2 * ‖M (b, 0) (b, 1)‖ ^ 2 ≤
          gramSpectralDefect
            (finitePartitionBlock part M b)
            (finitePartitionBlock_posSemidef part M hM b) := by
    intro b
    simpa [part] using
      v17_product_fiber_defect_ge_of_diag_re_le_one M hM hdiag b
  calc
    (∑ b : β, 2 * ‖M (b, 0) (b, 1)‖ ^ 2)
        ≤ ∑ b : β,
            gramSpectralDefect
              (finitePartitionBlock part M b)
              (finitePartitionBlock_posSemidef part M hM b) := by
            exact Finset.sum_le_sum fun b hb => hfiber b
    _ ≤ gramSpectralDefect M hM := hp

end ProductPairs

end HurtadoZeta23
