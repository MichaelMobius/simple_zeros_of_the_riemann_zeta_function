import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- A rational centre-radius enclosure. -/
def v26Ball (x c r : ℝ) : Prop := |x - c| ≤ r

lemma v26_ball_const (c : ℝ) : v26Ball c c 0 := by
  simp [v26Ball]

lemma v26_ball_radius_nonneg {x c r : ℝ} (h : v26Ball x c r) : 0 ≤ r := by
  unfold v26Ball at h
  exact (abs_nonneg (x - c)).trans h

lemma v26_ball_bounds {x c r : ℝ} (h : v26Ball x c r) :
    c - r ≤ x ∧ x ≤ c + r := by
  unfold v26Ball at h
  rw [abs_le] at h
  constructor <;> linarith

lemma v26_ball_of_bounds {x L U : ℝ} (hL : L ≤ x) (hU : x ≤ U) :
    v26Ball x ((L + U) / 2) ((U - L) / 2) := by
  unfold v26Ball
  rw [abs_le]
  constructor <;> linarith

lemma v26_ball_neg {x c r : ℝ} (h : v26Ball x c r) :
    v26Ball (-x) (-c) r := by
  unfold v26Ball at h ⊢
  simpa [abs_neg] using h

lemma v26_ball_add {x cx rx y cy ry : ℝ}
    (hx : v26Ball x cx rx) (hy : v26Ball y cy ry) :
    v26Ball (x + y) (cx + cy) (rx + ry) := by
  unfold v26Ball at hx hy ⊢
  have htri := abs_add (x - cx) (y - cy)
  have hid : (x + y) - (cx + cy) = (x - cx) + (y - cy) := by ring
  rw [hid]
  exact htri.trans (add_le_add hx hy)

lemma v26_ball_sub {x cx rx y cy ry : ℝ}
    (hx : v26Ball x cx rx) (hy : v26Ball y cy ry) :
    v26Ball (x - y) (cx - cy) (rx + ry) := by
  have hn := v26_ball_neg hy
  simpa [sub_eq_add_neg] using v26_ball_add hx hn

/-- Product rule for rational balls.  This is the only nonlinear interval
operation needed by the generated final-cell certificates. -/
lemma v26_ball_mul {x cx rx y cy ry : ℝ}
    (hx : v26Ball x cx rx) (hy : v26Ball y cy ry) :
    v26Ball (x * y) (cx * cy)
      (|cx| * ry + |cy| * rx + rx * ry) := by
  have hrx : 0 ≤ rx := v26_ball_radius_nonneg hx
  have hry : 0 ≤ ry := v26_ball_radius_nonneg hy
  unfold v26Ball at hx hy ⊢
  have hxy : |(x - cx) * (y - cy)| ≤ rx * ry := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hrx
  have hcx : |cx * (y - cy)| ≤ |cx| * ry := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg cx)
  have hcy : |cy * (x - cx)| ≤ |cy| * rx := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg cy)
  have hid :
      x * y - cx * cy =
        (x - cx) * (y - cy) + cx * (y - cy) + cy * (x - cx) := by
    ring
  rw [hid]
  calc
    |(x - cx) * (y - cy) + cx * (y - cy) + cy * (x - cx)|
        ≤ |(x - cx) * (y - cy) + cx * (y - cy)| + |cy * (x - cx)| :=
      abs_add _ _
    _ ≤ (|(x - cx) * (y - cy)| + |cx * (y - cy)|) + |cy * (x - cx)| := by
      gcongr
      exact abs_add _ _
    _ ≤ (rx * ry + |cx| * ry) + |cy| * rx := by linarith
    _ = |cx| * ry + |cy| * rx + rx * ry := by ring

lemma v26_ball_mul_const_left {x c r a : ℝ} (h : v26Ball x c r) :
    v26Ball (a * x) (a * c) (|a| * r) := by
  have hc := v26_ball_const a
  have hm := v26_ball_mul hc h
  simpa using hm

lemma v26_ball_mul_const_right {x c r a : ℝ} (h : v26Ball x c r) :
    v26Ball (x * a) (c * a) (|a| * r) := by
  have hm := v26_ball_mul h (v26_ball_const a)
  simpa [mul_comm] using hm

end HurtadoZeta23
