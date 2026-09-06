import HurtadoZeta23.ConcreteBlockDefect
import Mathlib.Tactic

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-- Entrywise diagonal control gives a trace control for a `450 × 450` complex
matrix.  Only real parts enter `RHLinalg.rtrace`. -/
theorem v17_rtrace_error_fin450
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    {eps : ℝ}
    (hdiag : ∀ i : Fin 450, |(G i i).re - 1| ≤ eps) :
    |RHLinalg.rtrace G - 450| ≤ 450 * eps := by
  have hid :
      RHLinalg.rtrace G - 450 =
        ∑ i : Fin 450, ((G i i).re - 1) := by
    unfold RHLinalg.rtrace Matrix.trace
    rw [map_sum]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hid]
  calc
    |∑ i : Fin 450, ((G i i).re - 1)|
        ≤ ∑ i : Fin 450, |(G i i).re - 1| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 450, eps := by
          apply Finset.sum_le_sum
          intro i hi
          exact hdiag i
    _ = 450 * eps := by
          simp

/-- The `eps ≤ 10^{-5}` regime gives exactly the trace tolerance consumed by
the robust finite spectral threshold. -/
theorem v17_rtrace_error_fin450_of_eps
    (G : Matrix (Fin 450) (Fin 450) ℂ)
    {eps : ℝ}
    (heps : eps ≤ 1 / 100000)
    (hdiag : ∀ i : Fin 450, |(G i i).re - 1| ≤ eps) :
    |RHLinalg.rtrace G - 450| ≤ 9 / 2000 := by
  have h := v17_rtrace_error_fin450 G hdiag
  norm_num at heps ⊢
  nlinarith

end HurtadoZeta23
