import HurtadoZeta23.V21KernelIntervalCurvature
import HurtadoZeta23.V21KernelRootWeight
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

noncomputable section

open Set

namespace HurtadoZeta23

/-- Phase measured from the integer centre of a kernel cell. -/
def v21CentralPhase (n : ℕ) (x : ℝ) : ℝ :=
  Real.pi * (x - (n : ℝ))

/-- Kernel with the alternating lobe sign removed.  Between the `n`th and
`(n+1)`st roots this is the positive lobe. -/
def v21SignedKernel (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * v21KernelX x

def v21SignedKernelPrime (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * v21KernelXPrime x

def v21SignedKernelSecond (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * v21KernelXSecond x

lemma v21_central_phase_bounds {n : ℕ} {x : ℝ}
    (hxL : (n : ℝ) + (3 / 20 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (17 / 20 : ℝ)) :
    (3 / 20 : ℝ) * Real.pi ≤ v21CentralPhase n x ∧
      v21CentralPhase n x ≤ (17 / 20 : ℝ) * Real.pi := by
  unfold v21CentralPhase
  constructor
  · have h := mul_le_mul_of_nonneg_left
      (show (3 / 20 : ℝ) ≤ x - (n : ℝ) by linarith) Real.pi_pos.le
    nlinarith
  · have h := mul_le_mul_of_nonneg_left
      (show x - (n : ℝ) ≤ (17 / 20 : ℝ) by linarith) Real.pi_pos.le
    nlinarith

lemma v21_signed_M2_phase_eq (n : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ n * v21M2 (v21B x) =
      v21P2 (v21B x) * Real.cos (v21CentralPhase n x) +
        v21Q2 (v21B x) * Real.sin (v21CentralPhase n x) := by
  let t : ℝ := v21CentralPhase n x
  have hB : v21B x = t + (n : ℝ) * Real.pi := by
    dsimp [t, v21CentralPhase]
    unfold v21B
    ring
  have hsin :
      Real.sin (v21B x) = (-1 : ℝ) ^ n * Real.sin t := by
    rw [hB]
    simpa using Real.sin_add_nat_mul_pi t n
  have hcos :
      Real.cos (v21B x) = (-1 : ℝ) ^ n * Real.cos t := by
    rw [hB]
    simpa using Real.cos_add_nat_mul_pi t n
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    norm_num
  unfold v21M2
  rw [hsin, hcos]
  dsimp [t]
  ring_nf
  simp [hs]

/-- On the right part of the central strip the elementary phase relation
`-cos t ≤ 2 sin t` has enough slack to pair with `Q₂ ≤ 2 P₂`. -/
lemma v21_central_negcos_le_two_sin {n : ℕ} {x : ℝ}
    (hxM : (n : ℝ) + (1 / 2 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (17 / 20 : ℝ)) :
    -Real.cos (v21CentralPhase n x) ≤
      2 * Real.sin (v21CentralPhase n x) := by
  let t : ℝ := v21CentralPhase n x
  let u : ℝ := Real.pi - t
  have htL : Real.pi / 2 ≤ t := by
    dsimp [t, v21CentralPhase]
    have h := mul_le_mul_of_nonneg_left
      (show (1 / 2 : ℝ) ≤ x - (n : ℝ) by linarith) Real.pi_pos.le
    nlinarith
  have htU : t ≤ (17 / 20 : ℝ) * Real.pi := by
    dsimp [t, v21CentralPhase]
    have h := mul_le_mul_of_nonneg_left
      (show x - (n : ℝ) ≤ (17 / 20 : ℝ) by linarith) Real.pi_pos.le
    nlinarith
  have hu0 : 0 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_pos, htU]
  have huU : u ≤ Real.pi / 2 := by
    dsimp [u]
    nlinarith
  have huL : (3 / 20 : ℝ) * Real.pi ≤ u := by
    dsimp [u]
    nlinarith
  let l : ℝ := v21RootPiL * (3 / 20 : ℝ)
  have hpiL : v21RootPiL ≤ Real.pi := by
    simpa [v21RootPiL] using (le_of_lt v21_pi_lower)
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num [v21RootPiL]
  have hl1 : l ≤ 1 := by dsimp [l]; norm_num [v21RootPiL]
  have hlu : l ≤ u := by
    dsimp [l]
    have hrat : v21RootPiL * (3 / 20 : ℝ) ≤
        Real.pi * (3 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_right hpiL (by norm_num)
    nlinarith
  have hsinTaylor := v21_sin_lower7 (x := l) hl0 hl1
  have hsinRat :
      (9 / 20 : ℝ) ≤
        l - l ^ 3 / 6 + l ^ 5 / 120 - l ^ 7 / 5040 := by
    dsimp [l]
    norm_num [v21RootPiL]
  have hsinMono : Real.sin l ≤ Real.sin u := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hl0]
    · exact huU
    · exact hlu
  have hsinL : (9 / 20 : ℝ) ≤ Real.sin u :=
    hsinRat.trans (hsinTaylor.trans hsinMono)
  have hucos : 0 ≤ Real.cos u := by
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos, hu0], huU⟩
  have hsinSq : (81 / 400 : ℝ) ≤ (Real.sin u) ^ 2 := by
    nlinarith [sq_nonneg (Real.sin u - (9 / 20 : ℝ))]
  have hid := Real.sin_sq_add_cos_sq u
  have hcosU : Real.cos u ≤ (9 / 10 : ℝ) := by
    by_contra h
    have hc : (9 / 10 : ℝ) < Real.cos u := lt_of_not_ge h
    have hp :
        0 < (Real.cos u - (9 / 10 : ℝ)) *
          (Real.cos u + (9 / 10 : ℝ)) := by
      exact mul_pos (sub_pos.mpr hc) (by nlinarith [hucos])
    nlinarith
  have htEq : t = Real.pi - u := by dsimp [u]; ring
  have hsinEq : Real.sin t = Real.sin u := by
    rw [htEq, Real.sin_pi_sub]
  have hcosEq : Real.cos t = -Real.cos u := by
    rw [htEq, Real.cos_pi_sub]
  dsimp [t] at hsinEq hcosEq ⊢
  rw [hsinEq, hcosEq]
  nlinarith

/-- After removing the alternating lobe sign, the cleared second derivative
is nonpositive throughout the universal central strip `[n+.15,n+.85]`. -/
lemma v21_signed_M2_nonpos_central {n : ℕ} (hn1 : 1 ≤ n) {x : ℝ}
    (hxL : (n : ℝ) + (3 / 20 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (17 / 20 : ℝ)) :
    (-1 : ℝ) ^ n * v21M2 (v21B x) ≤ 0 := by
  have hxpos : 0 < x := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    nlinarith
  have hb2 : 2 < v21B x := by
    unfold v21B
    nlinarith [mul_lt_mul_of_pos_right Real.pi_gt_three hxpos]
  have hP : v21P2 (v21B x) < 0 := v21_P2_neg_of_two_lt hb2
  have hQ : v21Q2 (v21B x) < 0 := v21_Q2_neg_of_two_lt hb2
  have heq := v21_signed_M2_phase_eq n x
  obtain ⟨htL, htU⟩ := v21_central_phase_bounds hxL hxU
  have ht0 : 0 ≤ v21CentralPhase n x := by
    nlinarith [Real.pi_pos, htL]
  have htPi : v21CentralPhase n x ≤ Real.pi := by
    nlinarith [Real.pi_pos, htU]
  have hsin : 0 ≤ Real.sin (v21CentralPhase n x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htPi
  by_cases hxM : x ≤ (n : ℝ) + (1 / 2 : ℝ)
  · have htM : v21CentralPhase n x ≤ Real.pi / 2 := by
      unfold v21CentralPhase
      have h := mul_le_mul_of_nonneg_left
        (show x - (n : ℝ) ≤ (1 / 2 : ℝ) by linarith) Real.pi_pos.le
      nlinarith
    have hcos : 0 ≤ Real.cos (v21CentralPhase n x) := by
      exact Real.cos_nonneg_of_mem_Icc
        ⟨by nlinarith [Real.pi_pos, ht0], htM⟩
    have h1 : v21P2 (v21B x) * Real.cos (v21CentralPhase n x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hP.le hcos
    have h2 : v21Q2 (v21B x) * Real.sin (v21CentralPhase n x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hQ.le hsin
    rw [heq]
    linarith
  · have hxM' : (n : ℝ) + (1 / 2 : ℝ) ≤ x := le_of_not_ge hxM
    have hrel := v21_central_negcos_le_two_sin hxM' hxU
    have hb47 : (47 / 10 : ℝ) ≤ v21B x := by
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hx15 : (3 / 2 : ℝ) ≤ x := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hx15 Real.pi_pos.le
      unfold v21B at hmul ⊢
      nlinarith [v21_pi_lower]
    have hQP := v21_Q2_le_two_P2 hb47
    have hmP : 0 ≤ -v21P2 (v21B x) := by linarith
    have hcosComp :
        v21P2 (v21B x) * Real.cos (v21CentralPhase n x) ≤
          -2 * v21P2 (v21B x) * Real.sin (v21CentralPhase n x) := by
      have h := mul_le_mul_of_nonneg_left hrel hmP
      nlinarith
    have hQComp :
        v21Q2 (v21B x) * Real.sin (v21CentralPhase n x) ≤
          2 * v21P2 (v21B x) * Real.sin (v21CentralPhase n x) :=
      mul_le_mul_of_nonneg_right hQP hsin
    rw [heq]
    nlinarith

lemma v21_signedKernel_hasDerivAt {n : ℕ} {x : ℝ}
    (hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt (v21SignedKernel n) (v21SignedKernelPrime n x) x := by
  simpa [v21SignedKernel, v21SignedKernelPrime] using
    (v21_kernelX_hasDerivAt hD).const_mul ((-1 : ℝ) ^ n)

lemma v21_signedKernelPrime_hasDerivAt {n : ℕ} {x : ℝ}
    (hD : (v21B x) ^ 2 - (1 / 2 : ℝ) ≠ 0) :
    HasDerivAt (v21SignedKernelPrime n) (v21SignedKernelSecond n x) x := by
  simpa [v21SignedKernelPrime, v21SignedKernelSecond] using
    (v21_kernelXPrime_hasDerivAt hD).const_mul ((-1 : ℝ) ^ n)

lemma v21_signedKernelSecond_nonpos_central {n : ℕ} (hn1 : 1 ≤ n) {x : ℝ}
    (hxL : (n : ℝ) + (3 / 20 : ℝ) ≤ x)
    (hxU : x ≤ (n : ℝ) + (17 / 20 : ℝ)) :
    v21SignedKernelSecond n x ≤ 0 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hxcert : v17KernelCertPoint < x := by
    have : (89 / 100 : ℝ) < x := by nlinarith
    simpa [v17KernelCertPoint] using this
  have hden := v21_kernel_den_pos_of_cert_lt hxcert
  have hm := v21_signed_M2_nonpos_central hn1 hxL hxU
  have hq :
      ((-1 : ℝ) ^ n * v21M2 (v21B x)) /
          ((v21B x) ^ 2 - (1 / 2 : ℝ)) ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hm (pow_nonneg hden.le 3)
  have hs := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Real.pi) hq
  unfold v21SignedKernelSecond v21KernelXSecond
  simpa [mul_assoc, mul_left_comm, mul_comm] using hs

/-- Universal central-lobe concavity.  This one theorem covers every gap
between the conservative univariate basins used later. -/
theorem v21_signedKernel_concave_central {n : ℕ} (hn1 : 1 ≤ n) :
    ConcaveOn ℝ
      (Icc ((n : ℝ) + (3 / 20 : ℝ)) ((n : ℝ) + (17 / 20 : ℝ)))
      (v21SignedKernel n) := by
  let D : Set ℝ :=
    Icc ((n : ℝ) + (3 / 20 : ℝ)) ((n : ℝ) + (17 / 20 : ℝ))
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
  · intro x hx
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hxcert : v17KernelCertPoint < x := by
      have : (89 / 100 : ℝ) < x := by nlinarith [hx.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_signedKernel_hasDerivAt
      (v21_kernel_den_ne_of_cert_lt hxcert)).continuousAt.continuousWithinAt
  · intro x hx
    have hxD : x ∈ D := interior_subset hx
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hxcert : v17KernelCertPoint < x := by
      dsimp [D] at hxD
      have : (89 / 100 : ℝ) < x := by nlinarith [hxD.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_signedKernel_hasDerivAt
      (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxD : x ∈ D := interior_subset hx
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hxcert : v17KernelCertPoint < x := by
      dsimp [D] at hxD
      have : (89 / 100 : ℝ) < x := by nlinarith [hxD.1]
      simpa [v17KernelCertPoint] using this
    exact (v21_signedKernelPrime_hasDerivAt
      (v21_kernel_den_ne_of_cert_lt hxcert)).hasDerivWithinAt
  · intro x hx
    have hxD : x ∈ D := interior_subset hx
    dsimp [D] at hxD
    exact v21_signedKernelSecond_nonpos_central hn1 hxD.1 hxD.2

end HurtadoZeta23
