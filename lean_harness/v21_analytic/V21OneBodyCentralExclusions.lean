import HurtadoZeta23.V21OneBodyFloors
import HurtadoZeta23.V21KernelCentralEndpointTable
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Generic bridge from a positive signed-kernel floor on a central lobe
interval to a one-body lower bound.  Position dependence enters only through
a rational pressure floor. -/
lemma v21_oneBody_ge_on_central_interval {j : Fin 6} {n : ℕ}
    {a b q p T x : ℝ}
    (hn1 : 1 ≤ n)
    (ha : a ∈ Icc ((n : ℝ) + (3 / 20 : ℝ))
      ((n : ℝ) + (17 / 20 : ℝ)))
    (hb : b ∈ Icc ((n : ℝ) + (3 / 20 : ℝ))
      ((n : ℝ) + (17 / 20 : ℝ)))
    (hx : x ∈ Icc a b)
    (hqa : q ≤ v21SignedKernel n a)
    (hqb : q ≤ v21SignedKernel n b)
    (hcertA : v17KernelCertPoint < a)
    (ha0 : 0 ≤ a) (hq0 : 0 ≤ q) (hp0 : 0 ≤ p)
    (hp : p ≤ pressure j)
    (harith : T ≤ p * a + (1 / 3 : ℝ) * q ^ 2) :
    T ≤ v21OneBody j x := by
  have hsig := v21_signedKernel_lower_on_central_interval
    hn1 ha hb hx hqa hqb
  have hxcert : v17KernelCertPoint < x := hcertA.trans_le hx.1
  have hw := v21_weight_lower_of_signedKernel_lower hxcert hq0 hsig
  have hx0 : 0 ≤ x := ha0.trans hx.1
  have hpa : p * a ≤ p * x := mul_le_mul_of_nonneg_left hx.1 hp0
  have hpx : p * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  unfold v21OneBody
  nlinarith

/-- Representative type-A exclusion: the interval between the second and
third retained root basins cannot occur below the type-A threshold. -/
theorem v21_oneBody_A_gap2 {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (2258 / 1000 : ℝ) ≤ x) (hxU : x ≤ (2612 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 2) (a := (2258 / 1000 : ℝ)) (b := (2612 / 1000 : ℝ))
    (q := (737 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_2258_lower
  · exact (by norm_num : (737 / 10000 : ℝ) ≤ 878 / 10000).trans
      v21_signed_at_2612_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · norm_num
  · exact hp
  · norm_num

/-- Representative type-C exclusion. -/
theorem v21_oneBody_C_gap2 {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (2251 / 1000 : ℝ) ≤ x) (hxU : x ≤ (2633 / 1000 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 2) (a := (2251 / 1000 : ℝ)) (b := (2633 / 1000 : ℝ))
    (q := (719 / 10000 : ℝ)) (p := (3553 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_2251_lower
  · exact (by norm_num : (719 / 10000 : ℝ) ≤ 846 / 10000).trans
      v21_signed_at_2633_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · norm_num
  · exact hp
  · norm_num

/-- The tiny type-B tail past the universal central concavity strip is still
excluded pointwise by the rational box estimate. -/
theorem v21_oneBody_B_tail5 {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (585 / 100 : ℝ) ≤ x) (hxU : x ≤ (21890 / 3733 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  have hsig := v21_signed_tail_B_lower hxL hxU
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  have hw := v21_weight_lower_of_signedKernel_lower hxcert
    (by norm_num : (0 : ℝ) ≤ 7 / 500) hsig
  have hx0 : 0 ≤ x := by nlinarith
  have hpL :
      (3733 / 10000000 : ℝ) * (585 / 100 : ℝ) ≤
        (3733 / 10000000 : ℝ) * x :=
    mul_le_mul_of_nonneg_left hxL (by norm_num)
  have hpx :
      (3733 / 10000000 : ℝ) * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  unfold v21OneBody
  nlinarith

end HurtadoZeta23
