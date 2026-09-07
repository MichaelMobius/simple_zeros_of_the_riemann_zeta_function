import HurtadoZeta23.V17ConcreteMatching450
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- The first coordinate of the canonical `225 × 2` pairing is the even
natural index `2*b`. -/
@[simp] theorem v17PairEquiv450_zero_val (b : Fin 225) :
    (v17PairEquiv450 (b, 0)).val = 2 * b.val := by
  simp [v17PairEquiv450, finProdFinEquiv]

/-- The second coordinate of the canonical `225 × 2` pairing is the odd
natural index `2*b+1`. -/
@[simp] theorem v17PairEquiv450_one_val (b : Fin 225) :
    (v17PairEquiv450 (b, 1)).val = 2 * b.val + 1 := by
  simp [v17PairEquiv450, finProdFinEquiv]

/-- For the first 224 blocks, rotating the even endpoint advances it to the
odd adjacent index. -/
@[simp] theorem v17_rotated_pair_zero_val (b : Fin 224) :
    (finRotate 450 (v17PairEquiv450 (b.castSucc, 0))).val = 2 * b.val + 1 := by
  rw [finRotate_apply]
  simp [Fin.add_def]
  omega

/-- For the first 224 blocks, rotating the odd endpoint advances it to the
next even adjacent index. -/
@[simp] theorem v17_rotated_pair_one_val (b : Fin 224) :
    (finRotate 450 (v17PairEquiv450 (b.castSucc, 1))).val = 2 * b.val + 2 := by
  rw [finRotate_apply]
  simp [Fin.add_def]
  omega

/-- The final rotated even endpoint is index 449. -/
@[simp] theorem v17_rotated_last_zero_val :
    (finRotate 450 (v17PairEquiv450 (Fin.last 224, 0))).val = 449 := by
  rw [finRotate_apply]
  norm_num [Fin.add_def]

/-- The final rotated odd endpoint wraps from index 449 back to zero. -/
@[simp] theorem v17_rotated_last_one_val :
    (finRotate 450 (v17PairEquiv450 (Fin.last 224, 1))).val = 0 := by
  have hlast : v17PairEquiv450 (Fin.last 224, 1) = Fin.last 449 := by
    apply Fin.ext
    simp
  rw [hlast, finRotate_last]
  rfl

end HurtadoZeta23
