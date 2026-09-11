import HurtadoZeta23.V21KernelSecondDerivatives
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- The cosine coefficient in the cleared second derivative is negative once
`b > 2`. -/
lemma v21_P2_neg_of_two_lt {b : ℝ} (hb : 2 < b) :
    v21P2 b < 0 := by
  have hc : 0 ≤ v21C - (1 / 2 : ℝ) := by
    linarith [v21_C_gt_half]
  have hbpos : 0 < b := by linarith
  have hb2 : 4 < b ^ 2 := by
    nlinarith [sq_nonneg (b - 2)]
  have hb4 : 16 < b ^ 4 := by
    have hs := sq_nonneg (b ^ 2 - 4)
    nlinarith
  have hcoef : -2 * b ^ 4 + (1 / 2 : ℝ) < 0 := by
    nlinarith
  have hprod :
      (-2 * b ^ 4 + (1 / 2 : ℝ)) *
          (v21C - (1 / 2 : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcoef) hc
  have hid :
      v21P2 b =
        (-2 * b ^ 4 + (1 / 2 : ℝ)) *
            (v21C - (1 / 2 : ℝ)) -
          (1 / 2 : ℝ) * b ^ 4 -
          (7 / 2 : ℝ) * b ^ 2 - (1 / 8 : ℝ) := by
    unfold v21P2
    ring
  rw [hid]
  nlinarith

/-- The sine coefficient in the cleared second derivative is negative once
`b > 2`. -/
lemma v21_Q2_neg_of_two_lt {b : ℝ} (hb : 2 < b) :
    v21Q2 b < 0 := by
  have hbpos : 0 < b := by linarith
  have hCpos : 0 < v21C := by linarith [v21_C_gt_half]
  have ht : 4 < b ^ 2 := by
    nlinarith [sq_nonneg (b - 2)]
  have hs : 0 ≤ (b ^ 2 - 4) ^ 2 := sq_nonneg _
  have hA :
      -b ^ 4 + 3 * b ^ 2 + (11 / 4 : ℝ) < 0 := by
    nlinarith
  have hB : 1 - 2 * b ^ 2 < 0 := by
    nlinarith
  have h1 :
      v21C * b *
          (-b ^ 4 + 3 * b ^ 2 + (11 / 4 : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hCpos hbpos) hA
  have h2 : b * (1 - 2 * b ^ 2) < 0 :=
    mul_neg_of_pos_of_neg hbpos hB
  have hid :
      v21Q2 b =
        v21C * b *
            (-b ^ 4 + 3 * b ^ 2 + (11 / 4 : ℝ)) +
          b * (1 - 2 * b ^ 2) := by
    unfold v21Q2
    ring
  rw [hid]
  linarith

/-- On the right half of the second lobe, the sine coefficient is at most
`2 P`.  The threshold `4.7` is deliberately rational and leaves large slack. -/
lemma v21_Q2_le_two_P2 {b : ℝ} (hb : (47 / 10 : ℝ) ≤ b) :
    v21Q2 b ≤ 2 * v21P2 b := by
  let u : ℝ := b - (47 / 10 : ℝ)
  let c : ℝ := v21C - (1 / 2 : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith [v21_C_gt_half]
  have h0 : 0 ≤ c * u ^ 5 := mul_nonneg hc (pow_nonneg hu 5)
  have h1 : 0 ≤ c * u ^ 4 := mul_nonneg hc (pow_nonneg hu 4)
  have h2 : 0 ≤ c * u ^ 3 := mul_nonneg hc (pow_nonneg hu 3)
  have h3 : 0 ≤ c * u ^ 2 := mul_nonneg hc (pow_nonneg hu 2)
  have h4 : 0 ≤ c * u := mul_nonneg hc hu
  have h5 : 0 ≤ c := hc
  have h6 : 0 ≤ u ^ 5 := pow_nonneg hu 5
  have h7 : 0 ≤ u ^ 4 := pow_nonneg hu 4
  have h8 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  have h9 : 0 ≤ u ^ 2 := pow_nonneg hu 2
  have hid :
      v21Q2 b - 2 * v21P2 b =
        -c * u ^ 5 - (39 / 2 : ℝ) * c * u ^ 4 -
          (1427 / 10 : ℝ) * c * u ^ 3 -
          (46577 / 100 : ℝ) * c * u ^ 2 -
          (46169 / 80 : ℝ) * c * u -
          (1818367 / 100000 : ℝ) * c -
          (1 / 2 : ℝ) * u ^ 5 - (43 / 4 : ℝ) * u ^ 4 -
          (1843 / 20 : ℝ) * u ^ 3 - (3093 / 8 : ℝ) * u ^ 2 -
          (3078353 / 4000 : ℝ) * u -
          (108925187 / 200000 : ℝ) := by
    dsimp [u, c]
    unfold v21Q2 v21P2
    ring
  have hdiff : v21Q2 b - 2 * v21P2 b ≤ 0 := by
    rw [hid]
    nlinarith
  linarith

/-- On the right half of the third lobe, the stronger comparison `Q ≤ P`
holds already from the rational threshold `7.4`. -/
lemma v21_Q2_le_P2 {b : ℝ} (hb : (74 / 10 : ℝ) ≤ b) :
    v21Q2 b ≤ v21P2 b := by
  let u : ℝ := b - (74 / 10 : ℝ)
  let c : ℝ := v21C - (1 / 2 : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith [v21_C_gt_half]
  have h0 : 0 ≤ c * u ^ 5 := mul_nonneg hc (pow_nonneg hu 5)
  have h1 : 0 ≤ c * u ^ 4 := mul_nonneg hc (pow_nonneg hu 4)
  have h2 : 0 ≤ c * u ^ 3 := mul_nonneg hc (pow_nonneg hu 3)
  have h3 : 0 ≤ c * u ^ 2 := mul_nonneg hc (pow_nonneg hu 2)
  have h4 : 0 ≤ c * u := mul_nonneg hc hu
  have h5 : 0 ≤ c := hc
  have h6 : 0 ≤ u ^ 5 := pow_nonneg hu 5
  have h7 : 0 ≤ u ^ 4 := pow_nonneg hu 4
  have h8 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  have h9 : 0 ≤ u ^ 2 := pow_nonneg hu 2
  have hid :
      v21Q2 b - v21P2 b =
        -c * u ^ 5 - 35 * c * u ^ 4 -
          (2427 / 5 : ℝ) * c * u ^ 3 -
          (83213 / 25 : ℝ) * c * u ^ 2 -
          (5627953 / 500 : ℝ) * c * u -
          (186965363 / 12500 : ℝ) * c -
          (1 / 2 : ℝ) * u ^ 5 - 18 * u ^ 4 -
          (519 / 2 : ℝ) * u ^ 3 - (46736 / 25 : ℝ) * u ^ 2 -
          (6714161 / 1000 : ℝ) * u -
          (59930977 / 6250 : ℝ) := by
    dsimp [u, c]
    unfold v21Q2 v21P2
    ring
  have hdiff : v21Q2 b - v21P2 b ≤ 0 := by
    rw [hid]
    nlinarith
  linarith

end HurtadoZeta23
