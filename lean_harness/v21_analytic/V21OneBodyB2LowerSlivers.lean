import HurtadoZeta23.V21OneBodyCentralExclusions
import HurtadoZeta23.V21KernelB2LowerEndpoints
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- The short interval between the coarse B2 lower edge and the type-A refined
edge is already above the type-A one-body threshold. -/
theorem v21_oneBody_A_B2_lower_sliver {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (179 / 100 : ℝ) ≤ x)
    (hxU : x ≤ (1792 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 1) (a := (179 / 100 : ℝ)) (b := (1792 / 1000 : ℝ))
    (q := (695 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (695 / 10000 : ℝ) ≤ 7 / 100).trans
      v21_signed1_at_1790_lower
  · exact v21_signed1_at_1792_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · norm_num
  · exact hp
  · norm_num

/-- The tight type-B lower sliver.  The rational endpoint floor `0.0676`
leaves a strictly positive margin over the type-B threshold. -/
theorem v21_oneBody_B_B2_lower_sliver {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (179 / 100 : ℝ) ≤ x)
    (hxU : x ≤ (1798 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 1) (a := (179 / 100 : ℝ)) (b := (1798 / 1000 : ℝ))
    (q := (676 / 10000 : ℝ)) (p := (3733 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (676 / 10000 : ℝ) ≤ 7 / 100).trans
      v21_signed1_at_1790_lower
  · exact v21_signed1_at_1798_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · norm_num
  · exact hp
  · norm_num

/-- Type-C analogue of the lower B2 sliver exclusion. -/
theorem v21_oneBody_C_B2_lower_sliver {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (179 / 100 : ℝ) ≤ x)
    (hxU : x ≤ (1797 / 1000 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 1) (a := (179 / 100 : ℝ)) (b := (1797 / 1000 : ℝ))
    (q := (679 / 10000 : ℝ)) (p := (3553 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (679 / 10000 : ℝ) ≤ 7 / 100).trans
      v21_signed1_at_1790_lower
  · exact v21_signed1_at_1797_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · norm_num
  · exact hp
  · norm_num

end HurtadoZeta23
