import HurtadoZeta23.V21KernelCentralEndpointBounds
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

private macro "central_endpoint" : tactic =>
  `(tactic|
    first
    | norm_num [v17KernelCertPoint, v21RootPiU, v21RootDenCap,
        v21RootCL, v21RootPiL]
    | (norm_num [v17KernelCertPoint, v21RootPiU, v21RootDenCap,
        v21RootCL, v21RootPiL] <;> positivity))

-- Type A and shared endpoints.
theorem v21_signed_at_2258_lower :
    (737 / 10000 : ℝ) ≤ v21SignedKernel 2 (2258 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (242 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_2612_lower :
    (878 / 10000 : ℝ) ≤ v21SignedKernel 2 (2612 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (112 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_3396_lower :
    (693 / 10000 : ℝ) ≤ v21SignedKernel 3 (3396 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (104 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_3502_lower :
    (713 / 10000 : ℝ) ≤ v21SignedKernel 3 (3502 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (2 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_4465_lower :
    (562 / 10000 : ℝ) ≤ v21SignedKernel 4 (4465 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (35 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_4500_lower :
    (561 / 10000 : ℝ) ≤ v21SignedKernel 4 (4500 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (0 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5466_lower :
    (462 / 10000 : ℝ) ≤ v21SignedKernel 5 (5466 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (34 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5500_lower :
    (462 / 10000 : ℝ) ≤ v21SignedKernel 5 (5500 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (0 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_6413_lower :
    (383 / 10000 : ℝ) ≤ v21SignedKernel 6 (6413 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (87 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_6576_lower :
    (377 / 10000 : ℝ) ≤ v21SignedKernel 6 (6576 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (76 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_7270_lower :
    (258 / 10000 : ℝ) ≤ v21SignedKernel 7 (7270 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (230 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_A_cap_lower :
    (287 / 10000 : ℝ) ≤ v21SignedKernel 7 (10405 / 1357 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (168 / 1000 : ℝ))
  all_goals central_endpoint

-- Type B endpoints.
theorem v21_signed_at_2249_lower :
    (714 / 10000 : ℝ) ≤ v21SignedKernel 2 (2249 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (251 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_2637_lower :
    (839 / 10000 : ℝ) ≤ v21SignedKernel 2 (2637 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (137 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_3358_lower :
    (664 / 10000 : ℝ) ≤ v21SignedKernel 3 (3358 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (142 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_3568_lower :
    (684 / 10000 : ℝ) ≤ v21SignedKernel 3 (3568 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (68 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_4375_lower :
    (530 / 10000 : ℝ) ≤ v21SignedKernel 4 (4375 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (125 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_4611_lower :
    (513 / 10000 : ℝ) ≤ v21SignedKernel 4 (4611 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (111 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5285_lower :
    (367 / 10000 : ℝ) ≤ v21SignedKernel 5 (5285 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (215 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5780_lower :
    (264 / 10000 : ℝ) ≤ v21SignedKernel 5 (5780 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (280 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5850_lower :
    (163 / 10000 : ℝ) ≤ v21SignedKernel 5 (5850 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (350 / 1000 : ℝ))
  all_goals central_endpoint

/-- Uniform certificate for the tiny type-B tail beyond the universal
concavity strip. -/
theorem v21_signed_tail_B_lower {x : ℝ}
    (hxL : (585 / 100 : ℝ) ≤ x)
    (hxU : x ≤ (21890 / 3733 : ℝ)) :
    (7 / 500 : ℝ) ≤ v21SignedKernel 5 x := by
  apply v21_signedKernel_central_box_lower
    (L := (585 / 100 : ℝ)) (U := (21890 / 3733 : ℝ))
    (r := (91 / 250 : ℝ))
  · have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  · norm_num
  · exact hxL
  · exact hxU
  · norm_num
  · norm_num
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith [hxU]
  · norm_num [v21RootPiU]
  · norm_num [v21RootDenCap, v21RootCL, v21RootPiL, v21RootPiU]

-- Type C endpoints.
theorem v21_signed_at_2251_lower :
    (719 / 10000 : ℝ) ≤ v21SignedKernel 2 (2251 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (249 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_2633_lower :
    (846 / 10000 : ℝ) ≤ v21SignedKernel 2 (2633 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (133 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_3365_lower :
    (670 / 10000 : ℝ) ≤ v21SignedKernel 3 (3365 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (135 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_3556_lower :
    (691 / 10000 : ℝ) ≤ v21SignedKernel 3 (3556 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (56 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_4392_lower :
    (540 / 10000 : ℝ) ≤ v21SignedKernel 4 (4392 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (108 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_4580_lower :
    (534 / 10000 : ℝ) ≤ v21SignedKernel 4 (4580 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (80 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5322_lower :
    (400 / 10000 : ℝ) ≤ v21SignedKernel 5 (5322 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (178 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5750_lower :
    (301 / 10000 : ℝ) ≤ v21SignedKernel 5 (5750 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (250 / 1000 : ℝ))
  all_goals central_endpoint

theorem v21_signed_at_5793_lower :
    (247 / 10000 : ℝ) ≤ v21SignedKernel 5 (5793 / 1000 : ℝ) := by
  apply v21_signedKernel_central_lower (r := (293 / 1000 : ℝ))
  all_goals central_endpoint

end HurtadoZeta23
