import HurtadoZeta23.BlockStability
import HurtadoZeta23.MatrixEnergy
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open scoped ComplexOrder BigOperators

/-- The scalar convex function used in the paper's Gram defect. -/
def psi (t : ℝ) : ℝ :=
  if t ≤ 2 then (t - 1)^2 else 2 * t - 3

lemma psi_eq_sq {t : ℝ} (ht : t ≤ 2) :
    psi t = (t - 1)^2 := by
  simp [psi, ht]

lemma psi_eq_linear {t : ℝ} (ht : 2 < t) :
    psi t = 2 * t - 3 := by
  simp [psi, not_le.mpr ht]

lemma psi_nonneg_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ psi t := by
  by_cases ht : t ≤ 2
  · rw [psi_eq_sq ht]
    positivity
  · have ht2 : 2 < t := lt_of_not_ge ht
    rw [psi_eq_linear ht2]
    linarith

lemma one_lt_psi_of_two_lt {t : ℝ} (ht : 2 < t) :
    1 < psi t := by
  rw [psi_eq_linear ht]
  linarith

/--
If one nonnegative eigenvalue is larger than two, the sum of all scalar defect
contributions is already strictly larger than one.

This is formulated for an arbitrary finite index type, rather than only
`Fin n`, so it can be applied directly to Mathlib matrices indexed by an
arbitrary finite type.
-/
lemma one_lt_sum_psi_of_exists_gt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (hlarge : ∃ i, 2 < lam i) :
    1 < ∑ i, psi (lam i) := by
  obtain ⟨k, hk⟩ := hlarge

  have hkpsi : 1 < psi (lam k) :=
    one_lt_psi_of_two_lt hk

  have hrest :
      0 ≤ ∑ i ∈ Finset.univ.erase k, psi (lam i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact psi_nonneg_of_nonneg (hlam0 i)

  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  linarith

/-- The small-spectrum Frobenius branch of the block-defect argument. -/
lemma small_spectrum_branch
    {D diagSq offDiag : ℝ}
    (hdiag : 0 ≤ diagSq)
    (hidentity : D = diagSq + offDiag) :
    offDiag ≤ D := by
  linarith

/-- The large-spectrum branch, expressed through the eigenvalue sum. -/
lemma large_spectrum_branch
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    (hlarge : ∃ i, 2 < lam i)
    {D : ℝ}
    (hD : D = ∑ i, psi (lam i)) :
    1 ≤ D := by
  rw [hD]
  exact le_of_lt
    (one_lt_sum_psi_of_exists_gt_two lam hlam0 hlarge)

/--
Pure logical core of the paper's Block defect lemma.

In the small-spectrum branch the Frobenius identity gives `offDiag ≤ D`.
In the large-spectrum branch a single eigenvalue above two gives `1 ≤ D`.
Either branch implies `min 1 offDiag ≤ D`.
-/
theorem block_defect_from_branches
    {D offDiag : ℝ}
    (hbranch : offDiag ≤ D ∨ 1 ≤ D) :
    min 1 offDiag ≤ D := by
  rcases hbranch with hoff | hone
  · exact le_trans (min_le_right 1 offDiag) hoff
  · exact le_trans (min_le_left 1 offDiag) hone

/--
Spectral/Frobenius formulation of Block defect.

The index type is an arbitrary finite type. This is important for matrix
applications, where Mathlib eigenvalues are naturally indexed by the original
finite row/column type rather than necessarily by `Fin n`.

When all eigenvalues are at most two, the remaining hypothesis identifies the
defect with the Frobenius square `diagSq + offDiag`. If an eigenvalue exceeds
two, the scalar definition of `psi` already forces defect at least one.
-/
theorem block_defect_spectral_core
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i)
    {D diagSq offDiag : ℝ}
    (hD : D = ∑ i, psi (lam i))
    (hdiag : 0 ≤ diagSq)
    (hsmallIdentity :
      (∀ i, lam i ≤ 2) →
        D = diagSq + offDiag) :
    min 1 offDiag ≤ D := by
  by_cases hsmall : ∀ i, lam i ≤ 2

  · apply block_defect_from_branches
    left
    exact small_spectrum_branch
      hdiag
      (hsmallIdentity hsmall)

  · push Not at hsmall
    apply block_defect_from_branches
    right
    exact large_spectrum_branch
      lam
      hlam0
      hsmall
      hD

/--
The exact scalar interface needed by `block_stability_262` once the actual Gram
matrix supplies its off-diagonal energy and the kernel approximation supplies
`E - err ≤ offDiag`.
-/
theorem block_stability_262_from_block_defect
    (y : ℕ → ℝ)
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hcert : SevenPointCertificate w y blockLength)
    (hmono : ∀ q < blockLength - 1, y q ≤ y (q + 1))
    (hspan0 : 0 ≤ y (blockLength - 1) - y 0)
    {D offDiag err : ℝ}
    (hD0 : 0 ≤ D)
    (herr : 0 ≤ err)
    (hblock : min 1 offDiag ≤ D)
    (hkernel :
      globalPairEnergyNat blockLength w - err ≤ offDiag) :
    A0 - err ≤
      D + beta * (y (blockLength - 1) - y 0) := by

  have hmin :
      min 1 (globalPairEnergyNat blockLength w - err)
        ≤ min 1 offDiag := by
    exact min_le_min_left 1 hkernel

  have hdefect :
      min 1 (globalPairEnergyNat blockLength w - err) ≤ D :=
    le_trans hmin hblock

  exact block_stability_262
    y
    w
    hw
    hcert
    hmono
    hspan0
    hD0
    herr
    hdefect

/--
Matrix-level Block defect reduction.

Compared with `block_defect_spectral_core`, nonnegativity of the eigenvalues is
obtained from Mathlib's PSD spectral theorem and the diagonal error is
eliminated using the proved Frobenius decomposition.

The only remaining small-spectrum bridge is the unitary-invariance statement

`sum psi(eigenvalues) = ‖G-I‖_F²`

when every eigenvalue lies in `[0,2]`.
-/
theorem block_defect_matrix_core
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ)
    (hG : G.IsHermitian)
    (hPSD : G.PosSemidef)
    {D : ℝ}
    (hD :
      D = ∑ i : n, psi (hG.eigenvalues i))
    (hsmallFrobenius :
      (∀ i : n, hG.eigenvalues i ≤ 2) →
        D = frobeniusDeviationSq G) :
    min 1 (offDiagonalEnergy G) ≤ D := by

  /-
  `PosSemidef` itself contains a proof of Hermitianity.  Its proof and `hG`
  are propositionally identical by proof irrelevance, so their eigenvalue
  families can be identified without making any mathematical assumption.
  -/
  have hHerm : hPSD.1 = hG := by
    apply Subsingleton.elim

  have hlam0 :
      ∀ i : n, 0 ≤ hG.eigenvalues i := by
    intro i
    rw [← hHerm]
    exact hPSD.eigenvalues_nonneg i

  apply block_defect_spectral_core
    (lam := hG.eigenvalues)
    hlam0
    hD
    (diagonalDeviationSq_nonneg G)

  intro hsmall
  rw [
    hsmallFrobenius hsmall,
    frobeniusDeviationSq_eq_diag_add_offdiag
  ]

end HurtadoZeta23