import HurtadoZeta23.V17AdjacentPair
import HurtadoZeta23.GramPinchingFinitePartition
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Adjacent-band pinching for the odd block size 289

The 288 adjacent edges split into two disjoint matchings of 144 edges.  The
first matching is `(0,1),(2,3),...,(286,287)` with the final coordinate 288 as
a singleton.  The second is obtained by cyclically rotating one place, giving
`(1,2),(3,4),...,(287,288)` with coordinate 0 as the singleton.
-/

/-- Partition `Fin 289` into 144 consecutive pairs and one final singleton. -/
def research9EvenPart289 (i : Fin 289) : Fin 145 := by
  refine ⟨i.val / 2, ?_⟩
  omega

/-- Even endpoint of pair `b`. -/
def research9EvenIndex0 (b : Fin 144) : Fin 289 :=
  ⟨2 * b.val, by omega⟩

/-- Odd endpoint of pair `b`. -/
def research9EvenIndex1 (b : Fin 144) : Fin 289 :=
  ⟨2 * b.val + 1, by omega⟩

/-- The non-singleton fibers of `research9EvenPart289` are canonically
`Fin 2`. -/
def research9EvenPairFiberEquiv (b : Fin 144) :
    {i : Fin 289 // research9EvenPart289 i = b.castSucc} ≃ Fin 2 where
  toFun i := ⟨i.1.val % 2, Nat.mod_lt _ (by omega)⟩
  invFun j := by
    refine ⟨⟨2 * b.val + j.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [research9EvenPart289]
    omega
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hp := congrArg Fin.val i.2
    simp [research9EvenPart289] at hp
    dsimp
    omega
  right_inv j := by
    apply Fin.ext
    dsimp
    omega

@[simp] theorem research9EvenPairFiberEquiv_symm_zero_val (b : Fin 144) :
    ((research9EvenPairFiberEquiv b).symm 0).1.val = 2 * b.val := by
  rfl

@[simp] theorem research9EvenPairFiberEquiv_symm_one_val (b : Fin 144) :
    ((research9EvenPairFiberEquiv b).symm 1).1.val = 2 * b.val + 1 := by
  rfl

/-- One pair fiber costs at least twice the squared off-diagonal entry under
the finite-safe diagonal condition. -/
theorem research9_even_pair_fiber_defect_ge
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1)
    (b : Fin 144) :
    2 * ‖G (research9EvenIndex0 b) (research9EvenIndex1 b)‖ ^ 2 ≤
      gramSpectralDefect
        (finitePartitionBlock research9EvenPart289 G b.castSucc)
        (finitePartitionBlock_posSemidef research9EvenPart289 G hG b.castSucc) := by
  let B := finitePartitionBlock research9EvenPart289 G b.castSucc
  let hB : B.PosSemidef :=
    finitePartitionBlock_posSemidef research9EvenPart289 G hG b.castSucc
  let e := research9EvenPairFiberEquiv b
  let B2 := Matrix.reindex e e B
  let hB2 : B2.PosSemidef := posSemidef_reindex e B hB
  have hsum :
      (G (research9EvenIndex0 b) (research9EvenIndex0 b)).re +
          (G (research9EvenIndex1 b) (research9EvenIndex1 b)).re ≤ 2 := by
    linarith [hdiag (research9EvenIndex0 b), hdiag (research9EvenIndex1 b)]
  have htrace : RHLinalg.rtrace B2 ≤ 2 := by
    unfold RHLinalg.rtrace Matrix.trace
    simpa [B2, B, e, research9EvenPairFiberEquiv,
      research9EvenIndex0, research9EvenIndex1,
      finitePartitionBlock, Matrix.reindex_apply] using hsum
  have h01 :
      B2 0 1 = G (research9EvenIndex0 b) (research9EvenIndex1 b) := by
    apply congrArg id
    simp [B2, B, e, research9EvenPairFiberEquiv,
      research9EvenIndex0, research9EvenIndex1,
      finitePartitionBlock, Matrix.reindex_apply]
  have hdef2 :=
    v17_fin2_gram_defect_ge_two_offdiag_of_rtrace_le B2 hB2 htrace
  have hre := gramSpectralDefect_reindex e B hB
  calc
    2 * ‖G (research9EvenIndex0 b) (research9EvenIndex1 b)‖ ^ 2
        = 2 * ‖B2 0 1‖ ^ 2 := by rw [h01]
    _ ≤ gramSpectralDefect B2 hB2 := hdef2
    _ = gramSpectralDefect B hB := hre

/-- The first 144-edge matching costs at most one copy of the full spectral
defect. -/
theorem research9_even_matching_fin289
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1) :
    (∑ b : Fin 144,
        2 * ‖G (research9EvenIndex0 b) (research9EvenIndex1 b)‖ ^ 2)
      ≤ gramSpectralDefect G hG := by
  let F : Fin 145 → ℝ := fun c =>
    gramSpectralDefect
      (finitePartitionBlock research9EvenPart289 G c)
      (finitePartitionBlock_posSemidef research9EvenPart289 G hG c)
  have hp := finitePartitionGramPinching_proved research9EvenPart289 G hG
  have hp' : (∑ c : Fin 145, F c) ≤ gramSpectralDefect G hG := by
    simpa [F] using hp
  rw [Fin.sum_univ_castSucc] at hp'
  have hpairs :
      (∑ b : Fin 144,
          2 * ‖G (research9EvenIndex0 b) (research9EvenIndex1 b)‖ ^ 2)
        ≤ ∑ b : Fin 144, F b.castSucc := by
    exact Finset.sum_le_sum fun b hb => by
      simpa [F] using research9_even_pair_fiber_defect_ge G hG hdiag b
  have hlast : 0 ≤ F (Fin.last 144) := by
    unfold F
    exact gramSpectralDefect_nonneg _ _
  linarith

/-- Rotating the first matching by one place gives the complementary 144-edge
matching `(1,2),...,(287,288)` and still costs at most one spectral defect. -/
theorem research9_rotated_matching_fin289
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1) :
    (∑ b : Fin 144,
        2 * ‖G (finRotate 289 (research9EvenIndex0 b))
              (finRotate 289 (research9EvenIndex1 b))‖ ^ 2)
      ≤ gramSpectralDefect G hG := by
  let r : Equiv.Perm (Fin 289) := finRotate 289
  let M : Matrix (Fin 289) (Fin 289) ℂ := Matrix.reindex r.symm r.symm G
  let hM : M.PosSemidef := posSemidef_reindex r.symm G hG
  have hdiagM : ∀ i, (M i i).re ≤ 1 := by
    intro i
    simpa [M, r, Matrix.reindex_apply] using hdiag (r i)
  have hp := research9_even_matching_fin289 M hM hdiagM
  have hre := gramSpectralDefect_reindex r.symm G hG
  calc
    (∑ b : Fin 144,
        2 * ‖G (finRotate 289 (research9EvenIndex0 b))
              (finRotate 289 (research9EvenIndex1 b))‖ ^ 2)
        = ∑ b : Fin 144,
            2 * ‖M (research9EvenIndex0 b) (research9EvenIndex1 b)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro b hb
              simp [M, r, Matrix.reindex_apply]
    _ ≤ gramSpectralDefect M hM := hp
    _ = gramSpectralDefect G hG := hre

/-- Canonical equivalence used to split the 288 edge indices into even and odd
positions. -/
def research9EdgeEquiv288 : Fin 144 × Fin 2 ≃ Fin 288 := by
  simpa using (finProdFinEquiv : Fin 144 × Fin 2 ≃ Fin (144 * 2))

@[simp] theorem research9EdgeEquiv288_zero_val (b : Fin 144) :
    (research9EdgeEquiv288 (b, 0)).val = 2 * b.val := by
  simp [research9EdgeEquiv288, finProdFinEquiv]

@[simp] theorem research9EdgeEquiv288_one_val (b : Fin 144) :
    (research9EdgeEquiv288 (b, 1)).val = 2 * b.val + 1 := by
  simp [research9EdgeEquiv288, finProdFinEquiv]
  omega

@[simp] theorem research9_rotated_even_zero_val (b : Fin 144) :
    (finRotate 289 (research9EvenIndex0 b)).val = 2 * b.val + 1 := by
  rw [finRotate_apply]
  simp [Fin.add_def, research9EvenIndex0]
  omega

@[simp] theorem research9_rotated_even_one_val (b : Fin 144) :
    (finRotate 289 (research9EvenIndex1 b)).val = 2 * b.val + 2 := by
  rw [finRotate_apply]
  simp [Fin.add_def, research9EvenIndex1]
  omega

/-- Natural 288-edge adjacent energy of a 289-by-289 Gram matrix. -/
def research9AdjacentEnergy289 (G : Matrix (Fin 289) (Fin 289) ℂ) : ℝ :=
  ∑ r : Fin 288,
    ‖G ⟨r.val, by omega⟩ ⟨r.val + 1, by omega⟩‖ ^ 2

/-- Exact parity split of the natural adjacent band. -/
theorem research9_adjacent_energy_split
    (G : Matrix (Fin 289) (Fin 289) ℂ) :
    research9AdjacentEnergy289 G =
      (∑ b : Fin 144,
        ‖G (research9EvenIndex0 b) (research9EvenIndex1 b)‖ ^ 2) +
      (∑ b : Fin 144,
        ‖G (finRotate 289 (research9EvenIndex0 b))
            (finRotate 289 (research9EvenIndex1 b))‖ ^ 2) := by
  unfold research9AdjacentEnergy289
  rw [← Equiv.sum_comp research9EdgeEquiv288]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro b hb
    simp [research9EvenIndex0, research9EvenIndex1]
  · apply Finset.sum_congr rfl
    intro b hb
    simp [research9EvenIndex0, research9EvenIndex1]

/-- The complete 288-edge adjacent band costs at most one copy of the spectral
defect. -/
theorem research9_adjacent_matrix_band_le_defect_289
    (G : Matrix (Fin 289) (Fin 289) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i : Fin 289, (G i i).re ≤ 1) :
    research9AdjacentEnergy289 G ≤ gramSpectralDefect G hG := by
  have heven := research9_even_matching_fin289 G hG hdiag
  have hodd := research9_rotated_matching_fin289 G hG hdiag
  rw [← Finset.mul_sum] at heven hodd
  rw [research9_adjacent_energy_split]
  linarith

end HurtadoZeta23
