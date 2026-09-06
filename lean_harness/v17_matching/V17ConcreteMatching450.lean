import HurtadoZeta23.V17AdjacentMatching
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- Canonical pairing of the 450 coordinates into 225 consecutive pairs. -/
def v17PairEquiv450 : Fin 225 × Fin 2 ≃ Fin 450 := by
  simpa using (finProdFinEquiv : Fin 225 × Fin 2 ≃ Fin (225 * 2))

/-- The even matching `(0,1),(2,3),...,(448,449)` is controlled by the
spectral defect for every PSD finite Gram matrix with diagonal real parts at
most one. -/
theorem v17_even_matching_fin450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i, (G i i).re ≤ 1) :
    (∑ b : Fin 225,
        2 * ‖G (v17PairEquiv450 (b, 0)) (v17PairEquiv450 (b, 1))‖ ^ 2)
      ≤ gramSpectralDefect G hG := by
  let e := v17PairEquiv450
  let M : Matrix (Fin 225 × Fin 2) (Fin 225 × Fin 2) ℂ :=
    Matrix.reindex e.symm e.symm G
  let hM : M.PosSemidef := posSemidef_reindex e.symm G hG
  have hdiagM : ∀ i, (M i i).re ≤ 1 := by
    intro i
    simpa [M, Matrix.reindex_apply] using hdiag (e i)
  have hp := v17_product_pair_pinching_of_diag_re_le_one M hM hdiagM
  have hre := gramSpectralDefect_reindex e.symm G hG
  calc
    (∑ b : Fin 225,
        2 * ‖G (v17PairEquiv450 (b, 0)) (v17PairEquiv450 (b, 1))‖ ^ 2)
        = ∑ b : Fin 225, 2 * ‖M (b, 0) (b, 1)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro b hb
            simp [M, e, Matrix.reindex_apply]
    _ ≤ gramSpectralDefect M hM := hp
    _ = gramSpectralDefect G hG := hre

/-- The same matching after one cyclic rotation.  In the original coordinates
this consists of `(1,2),(3,4),...,(447,448)` together with the harmless wrap
pair `(449,0)`. -/
theorem v17_rotated_matching_fin450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    (hG : G.PosSemidef)
    (hdiag : ∀ i, (G i i).re ≤ 1) :
    (∑ b : Fin 225,
        2 * ‖G (finRotate 450 (v17PairEquiv450 (b, 0)))
              (finRotate 450 (v17PairEquiv450 (b, 1)))‖ ^ 2)
      ≤ gramSpectralDefect G hG := by
  let r : Equiv.Perm (Fin 450) := finRotate 450
  let M : Matrix (Fin 450) (Fin 450) ℂ := Matrix.reindex r.symm r.symm G
  let hM : M.PosSemidef := posSemidef_reindex r.symm G hG
  have hdiagM : ∀ i, (M i i).re ≤ 1 := by
    intro i
    simpa [M, Matrix.reindex_apply] using hdiag (r i)
  have hp := v17_even_matching_fin450 M hM hdiagM
  have hre := gramSpectralDefect_reindex r.symm G hG
  calc
    (∑ b : Fin 225,
        2 * ‖G (finRotate 450 (v17PairEquiv450 (b, 0)))
              (finRotate 450 (v17PairEquiv450 (b, 1)))‖ ^ 2)
        = ∑ b : Fin 225,
            2 * ‖M (v17PairEquiv450 (b, 0))
                  (v17PairEquiv450 (b, 1))‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro b hb
              simp [M, r, Matrix.reindex_apply]
    _ ≤ gramSpectralDefect M hM := hp
    _ = gramSpectralDefect G hG := hre

end HurtadoZeta23
