import HurtadoZeta23.V21OneBodyFloors
import HurtadoZeta23.V21KernelCentralEndpointTable
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Generic bridge from a signed-kernel floor on a central lobe interval to a
one-body lower bound.  All position dependence enters only through a rational
lower bound `p ≤ pressure j`. -/
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
    (ha0 : 0 ≤ a) (hp0 : 0 ≤ p) (hp : p ≤ pressure j)
    (harith : T ≤ p * a + (1 / 3 : ℝ) * q ^ 2) :
    T ≤ v21OneBody j x := by
  have hsig := v21_signedKernel_lower_on_central_interval
    hn1 ha hb hx hqa hqb
  have hxcert : v17KernelCertPoint < x := hcertA.trans_le hx.1
  have hw := v21_weight_lower_of_signedKernel_lower hxcert
    (by nlinarith [harith, hp0]) hsig
  have hx0 : 0 ≤ x := ha0.trans hx.1
  have hpa : p * a ≤ p * x := mul_le_mul_of_nonneg_left hx.1 hp0
  have hpx : p * x ≤ pressure j * x :=
    mul_le_mul_of_nonneg_right hp hx0
  unfold v21OneBody
  nlinarith

-- Type A = coordinates 0 and 5; pressure floor 2714 / 10^7.
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
  · exact hp
  · norm_num

theorem v21_oneBody_A_gap3 {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (3396 / 1000 : ℝ) ≤ x) (hxU : x ≤ (3502 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 3) (a := (3396 / 1000 : ℝ)) (b := (3502 / 1000 : ℝ))
    (q := (693 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_3396_lower
  · exact (by norm_num : (693 / 10000 : ℝ) ≤ 713 / 10000).trans
      v21_signed_at_3502_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_A_gap4 {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (4465 / 1000 : ℝ) ≤ x) (hxU : x ≤ (4500 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 4) (a := (4465 / 1000 : ℝ)) (b := (4500 / 1000 : ℝ))
    (q := (561 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (561 / 10000 : ℝ) ≤ 562 / 10000).trans
      v21_signed_at_4465_lower
  · exact v21_signed_at_4500_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_A_gap5 {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (5466 / 1000 : ℝ) ≤ x) (hxU : x ≤ (5500 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 5) (a := (5466 / 1000 : ℝ)) (b := (5500 / 1000 : ℝ))
    (q := (462 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_5466_lower
  · exact v21_signed_at_5500_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_A_gap6 {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (6413 / 1000 : ℝ) ≤ x) (hxU : x ≤ (6576 / 1000 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 6) (a := (6413 / 1000 : ℝ)) (b := (6576 / 1000 : ℝ))
    (q := (377 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (377 / 10000 : ℝ) ≤ 383 / 10000).trans
      v21_signed_at_6413_lower
  · exact v21_signed_at_6576_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_A_tail7 {j : Fin 6} {x : ℝ}
    (hp : (2714 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (7270 / 1000 : ℝ) ≤ x) (hxU : x ≤ (10405 / 1357 : ℝ)) :
    (2081 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 7) (a := (7270 / 1000 : ℝ)) (b := (10405 / 1357 : ℝ))
    (q := (258 / 10000 : ℝ)) (p := (2714 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_7270_lower
  · exact (by norm_num : (258 / 10000 : ℝ) ≤ 287 / 10000).trans
      v21_signed_at_A_cap_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

-- Type B = coordinates 1 and 4; pressure floor 3733 / 10^7.
theorem v21_oneBody_B_gap2 {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (2249 / 1000 : ℝ) ≤ x) (hxU : x ≤ (2637 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 2) (a := (2249 / 1000 : ℝ)) (b := (2637 / 1000 : ℝ))
    (q := (714 / 10000 : ℝ)) (p := (3733 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_2249_lower
  · exact (by norm_num : (714 / 10000 : ℝ) ≤ 839 / 10000).trans
      v21_signed_at_2637_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_B_gap3 {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (3358 / 1000 : ℝ) ≤ x) (hxU : x ≤ (3568 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 3) (a := (3358 / 1000 : ℝ)) (b := (3568 / 1000 : ℝ))
    (q := (664 / 10000 : ℝ)) (p := (3733 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_3358_lower
  · exact (by norm_num : (664 / 10000 : ℝ) ≤ 684 / 10000).trans
      v21_signed_at_3568_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_B_gap4 {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (4375 / 1000 : ℝ) ≤ x) (hxU : x ≤ (4611 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 4) (a := (4375 / 1000 : ℝ)) (b := (4611 / 1000 : ℝ))
    (q := (513 / 10000 : ℝ)) (p := (3733 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (513 / 10000 : ℝ) ≤ 530 / 10000).trans
      v21_signed_at_4375_lower
  · exact v21_signed_at_4611_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_B_gap5a {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (5285 / 1000 : ℝ) ≤ x) (hxU : x ≤ (5780 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 5) (a := (5285 / 1000 : ℝ)) (b := (5780 / 1000 : ℝ))
    (q := (264 / 10000 : ℝ)) (p := (3733 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (264 / 10000 : ℝ) ≤ 367 / 10000).trans
      v21_signed_at_5285_lower
  · exact v21_signed_at_5780_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_B_gap5b {j : Fin 6} {x : ℝ}
    (hp : (3733 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (5780 / 1000 : ℝ) ≤ x) (hxU : x ≤ (5850 / 1000 : ℝ)) :
    (2189 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 5) (a := (5780 / 1000 : ℝ)) (b := (5850 / 1000 : ℝ))
    (q := (163 / 10000 : ℝ)) (p := (3733 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (163 / 10000 : ℝ) ≤ 264 / 10000).trans
      v21_signed_at_5780_lower
  · exact v21_signed_at_5850_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

/-- The tiny remaining type-B pressure tail, handled pointwise rather than by
central-lobe concavity. -/
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

-- Type C = coordinates 2 and 3; pressure floor 3553 / 10^7.
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
  · exact hp
  · norm_num

theorem v21_oneBody_C_gap3 {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (3365 / 1000 : ℝ) ≤ x) (hxU : x ≤ (3556 / 1000 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 3) (a := (3365 / 1000 : ℝ)) (b := (3556 / 1000 : ℝ))
    (q := (670 / 10000 : ℝ)) (p := (3553 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact v21_signed_at_3365_lower
  · exact (by norm_num : (670 / 10000 : ℝ) ≤ 691 / 10000).trans
      v21_signed_at_3556_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_C_gap4 {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (4392 / 1000 : ℝ) ≤ x) (hxU : x ≤ (4580 / 1000 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 4) (a := (4392 / 1000 : ℝ)) (b := (4580 / 1000 : ℝ))
    (q := (534 / 10000 : ℝ)) (p := (3553 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (534 / 10000 : ℝ) ≤ 540 / 10000).trans
      v21_signed_at_4392_lower
  · exact v21_signed_at_4580_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_C_gap5a {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (5322 / 1000 : ℝ) ≤ x) (hxU : x ≤ (5750 / 1000 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 5) (a := (5322 / 1000 : ℝ)) (b := (5750 / 1000 : ℝ))
    (q := (301 / 10000 : ℝ)) (p := (3553 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (301 / 10000 : ℝ) ≤ 400 / 10000).trans
      v21_signed_at_5322_lower
  · exact v21_signed_at_5750_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

theorem v21_oneBody_C_gap5b {j : Fin 6} {x : ℝ}
    (hp : (3553 / 10000000 : ℝ) ≤ pressure j)
    (hxL : (5750 / 1000 : ℝ) ≤ x) (hxU : x ≤ (5793 / 1000 : ℝ)) :
    (2170 / 1000000 : ℝ) ≤ v21OneBody j x := by
  apply v21_oneBody_ge_on_central_interval
    (n := 5) (a := (5750 / 1000 : ℝ)) (b := (5793 / 1000 : ℝ))
    (q := (247 / 10000 : ℝ)) (p := (3553 / 10000000 : ℝ))
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨hxL, hxU⟩
  · exact (by norm_num : (247 / 10000 : ℝ) ≤ 301 / 10000).trans
      v21_signed_at_5750_lower
  · exact v21_signed_at_5793_lower
  · norm_num [v17KernelCertPoint]
  · norm_num
  · norm_num
  · exact hp
  · norm_num

end HurtadoZeta23
