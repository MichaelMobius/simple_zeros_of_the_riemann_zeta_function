import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- A point of `[L,U]` is no farther from `q` than the farther endpoint. -/
theorem v26_interval_abs_sub_le_max {L U x q : ℝ}
    (hLx : L ≤ x) (hxU : x ≤ U) :
    |x - q| ≤ max |L - q| |U - q| := by
  rcases le_total q x with hqx | hxq
  · rw [abs_of_nonneg (sub_nonneg.mpr hqx)]
    have h1 : x - q ≤ U - q := sub_le_sub_right hxU q
    have h2 : U - q ≤ |U - q| := le_abs_self _
    exact h1.trans (h2.trans (le_max_right _ _))
  · rw [abs_of_nonpos (sub_nonpos.mpr hxq)]
    have h1 : q - x ≤ q - L := sub_le_sub_left hLx q
    have h2 : q - L = -(L - q) := by ring
    rw [h2]
    exact h1.trans ((neg_le_abs _).trans (le_max_left _ _))

/-- Root brackets turn the endpoint radius around `q` into a radius around the
true root `r`, with an explicit safety pad `eps`. -/
theorem v26_interval_root_distance_le {L U x r q eps : ℝ}
    (hLx : L ≤ x) (hxU : x ≤ U)
    (heps : 0 ≤ eps) (hrq : |r - q| ≤ eps) :
    |x - r| ≤ max |L - q| |U - q| + eps := by
  have htri : |x - r| ≤ |x - q| + |r - q| := by
    have h := abs_add_le (x - q) (q - r)
    have hsum : (x - q) + (q - r) = x - r := by ring
    rw [hsum, abs_sub_comm q r] at h
    exact h
  have hxq := v26_interval_abs_sub_le_max hLx hxU (q := q)
  linarith

end HurtadoZeta23
