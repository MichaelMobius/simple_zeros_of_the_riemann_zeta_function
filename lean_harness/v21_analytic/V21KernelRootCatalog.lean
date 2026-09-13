import HurtadoZeta23.V21KernelRootSlope
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Rational left endpoints of the twelve certified positive-root brackets. -/
def v21RootLeft : ℕ → ℝ
  | 1 => 105727 / 100000
  | 2 => 203006 / 100000
  | 3 => 302024 / 100000
  | 4 => 401523 / 100000
  | 5 => 501220 / 100000
  | 6 => 601018 / 100000
  | 7 => 700873 / 100000
  | 8 => 800764 / 100000
  | 9 => 900679 / 100000
  | 10 => 1000611 / 100000
  | 11 => 1100556 / 100000
  | 12 => 1200509 / 100000
  | _ => 0

/-- Rational right endpoints of the twelve certified positive-root brackets. -/
def v21RootRight : ℕ → ℝ
  | 1 => 105728 / 100000
  | 2 => 203007 / 100000
  | 3 => 302025 / 100000
  | 4 => 401524 / 100000
  | 5 => 501221 / 100000
  | 6 => 601019 / 100000
  | 7 => 700874 / 100000
  | 8 => 800765 / 100000
  | 9 => 900680 / 100000
  | 10 => 1000612 / 100000
  | 11 => 1100557 / 100000
  | 12 => 1200510 / 100000
  | _ => 0

/-- Rational midpoint of the certified bracket. -/
def v21RootMid (n : ℕ) : ℝ := (v21RootLeft n + v21RootRight n) / 2

lemma v21_root_width {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootRight n - v21RootLeft n = (1 / 100000 : ℝ) := by
  interval_cases n <;> norm_num [v21RootLeft, v21RootRight]

lemma v21_root_mid_sub_left {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootMid n - v21RootLeft n = (1 / 200000 : ℝ) := by
  unfold v21RootMid
  have h := v21_root_width hn1 hn12
  linarith

lemma v21_root_right_sub_mid {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootRight n - v21RootMid n = (1 / 200000 : ℝ) := by
  unfold v21RootMid
  have h := v21_root_width hn1 hn12
  linarith

lemma v21_root_left_cell {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    (n : ℝ) - (1 / 20 : ℝ) ≤ v21RootLeft n := by
  interval_cases n <;> norm_num [v21RootLeft]

lemma v21_root_right_cell {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootRight n ≤ (n : ℝ) + (151 / 1000 : ℝ) := by
  interval_cases n <;> norm_num [v21RootRight]

/-- Uniform access to the twelve left-endpoint sign certificates. -/
lemma v21_root_left_sign {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    v21RootH n (v21RootLeft n) ≤ -(7 / 100000 : ℝ) := by
  interval_cases n
  · simpa [v21RootLeft] using v21_rootH_one_left
  · simpa [v21RootLeft] using v21_rootH_two_left
  · simpa [v21RootLeft] using v21_rootH_three_left
  · simpa [v21RootLeft] using v21_rootH_four_left
  · simpa [v21RootLeft] using v21_rootH_five_left
  · simpa [v21RootLeft] using v21_rootH_six_left
  · simpa [v21RootLeft] using v21_rootH_seven_left
  · simpa [v21RootLeft] using v21_rootH_eight_left
  · simpa [v21RootLeft] using v21_rootH_nine_left
  · simpa [v21RootLeft] using v21_rootH_ten_left
  · simpa [v21RootLeft] using v21_rootH_eleven_left
  · simpa [v21RootLeft] using v21_rootH_twelve_left

/-- Uniform access to the twelve right-endpoint sign certificates. -/
lemma v21_root_right_sign {n : ℕ} (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    (1 / 100000 : ℝ) ≤ v21RootH n (v21RootRight n) := by
  interval_cases n
  · simpa [v21RootRight] using v21_rootH_one_right
  · simpa [v21RootRight] using v21_rootH_two_right
  · simpa [v21RootRight] using v21_rootH_three_right
  · simpa [v21RootRight] using v21_rootH_four_right
  · simpa [v21RootRight] using v21_rootH_five_right
  · simpa [v21RootRight] using v21_rootH_six_right
  · simpa [v21RootRight] using v21_rootH_seven_right
  · simpa [v21RootRight] using v21_rootH_eight_right
  · simpa [v21RootRight] using v21_rootH_nine_right
  · simpa [v21RootRight] using v21_rootH_ten_right
  · simpa [v21RootRight] using v21_rootH_eleven_right
  · simpa [v21RootRight] using v21_rootH_twelve_right

end HurtadoZeta23
