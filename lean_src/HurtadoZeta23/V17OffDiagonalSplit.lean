import HurtadoZeta23.MatrixEnergy
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- Strict upper-triangular squared-entry energy. -/
def v17StrictUpperEnergy (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2

/-- Strict lower-triangular squared-entry energy. -/
def v17StrictLowerEnergy (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Iio i, ‖G i j‖ ^ 2

lemma v17_univ_erase_eq_Iio_union_Ioi
    {n : ℕ} (i : Fin n) :
    (Finset.univ.erase i : Finset (Fin n)) = Finset.Iio i ∪ Finset.Ioi i := by
  ext j
  simp [lt_or_lt_iff_ne]

lemma v17_Iio_Ioi_disjoint
    {n : ℕ} (i : Fin n) :
    Disjoint (Finset.Iio i) (Finset.Ioi i) := by
  rw [Finset.disjoint_left]
  intro j hjlo jhi
  exact (Finset.mem_Iio.mp hjlo).asymm (Finset.mem_Ioi.mp jhi)

/-- The directed off-diagonal energy is lower plus upper triangular energy. -/
theorem v17_offDiagonalEnergy_eq_lower_add_upper
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) :
    offDiagonalEnergy G = v17StrictLowerEnergy n G + v17StrictUpperEnergy n G := by
  unfold offDiagonalEnergy v17StrictLowerEnergy v17StrictUpperEnergy
  calc
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), ‖G i j‖ ^ 2)
        = ∑ i : Fin n,
            ((∑ j ∈ Finset.Iio i, ‖G i j‖ ^ 2) +
             (∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [v17_univ_erase_eq_Iio_union_Ioi i,
                Finset.sum_union (v17_Iio_Ioi_disjoint i)]
    _ = (∑ i : Fin n, ∑ j ∈ Finset.Iio i, ‖G i j‖ ^ 2) +
        (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2) := by
          rw [Finset.sum_add_distrib]

/-- Swapping the two indices identifies lower and upper triangular energy
whenever entry norms are symmetric. -/
theorem v17_strictLower_eq_strictUpper_of_norm_symm
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : ∀ i j, ‖G i j‖ = ‖G j i‖) :
    v17StrictLowerEnergy n G = v17StrictUpperEnergy n G := by
  unfold v17StrictLowerEnergy v17StrictUpperEnergy
  have hIio (i : Fin n) :
      Finset.Iio i = Finset.univ.filter (fun j : Fin n => j < i) := by
    ext j
    simp
  have hIoi (i : Fin n) :
      Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i < j) := by
    ext j
    simp
  simp_rw [hIio, hIoi, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : j < i
  · simp [h, hsymm i j]
  · simp [h]

/-- For norm-symmetric matrices the directed off-diagonal energy is exactly
twice the strict upper-triangular energy. -/
theorem v17_offDiagonalEnergy_eq_two_upper_of_norm_symm
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : ∀ i j, ‖G i j‖ = ‖G j i‖) :
    offDiagonalEnergy G = 2 * v17StrictUpperEnergy n G := by
  rw [v17_offDiagonalEnergy_eq_lower_add_upper,
    v17_strictLower_eq_strictUpper_of_norm_symm G hsymm]
  ring

end HurtadoZeta23
