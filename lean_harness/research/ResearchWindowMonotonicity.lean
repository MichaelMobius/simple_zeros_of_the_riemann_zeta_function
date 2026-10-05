import HurtadoZeta23.ResearchWindowActual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# Exact Bernstein certificate for the pinned research window

This file internalizes the exact-rational polynomial part of the
window-monotonicity certificate.  No floating-point arithmetic is used.
-/

def research9MonotonicityP (c : Real) : Real :=
  (-4325471 / 500000000 : Real)
    + (5589009 / 250000000 : Real) * c
    + (14389581 / 125000000 : Real) * c ^ 2
    + (-1894909 / 7812500 : Real) * c ^ 3
    + (-420143 / 3125000 : Real) * c ^ 4
    + (85602 / 390625 : Real) * c ^ 5

private lemma research9_bernstein5_nonneg
    (t b0 b1 b2 b3 b4 b5 : Real)
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hb0 : 0 <= b0) (hb1 : 0 <= b1)
    (hb2 : 0 <= b2) (hb3 : 0 <= b3)
    (hb4 : 0 <= b4) (hb5 : 0 <= b5) :
    0 <=
      b0 * (1 - t) ^ 5
      + 5 * b1 * t * (1 - t) ^ 4
      + 10 * b2 * t ^ 2 * (1 - t) ^ 3
      + 10 * b3 * t ^ 3 * (1 - t) ^ 2
      + 5 * b4 * t ^ 4 * (1 - t)
      + b5 * t ^ 5 := by
  have ht' : 0 <= 1 - t := by linarith
  positivity

/-- Exact polynomial bound used by the research-window monotonicity proof. -/
theorem research9MonotonicityP_ge
    {c : Real}
    (hcL : -1 <= c)
    (hcU : c <= 1) :
    (-161 / 5000 : Real) <= research9MonotonicityP c := by
  by_cases h0 : c <= (-6 / 7 : Real)
  ·
    have hl : (-1 : Real) <= c := by
      exact hcL
    have hu : c <= (-6 / 7 : Real) := by
      exact h0
    let t : Real := 7 * (c - (-1 : Real))
    have ht0 : 0 <= t := by
      dsimp [t]
      linarith
    have ht1 : t <= 1 := by
      dsimp [t]
      linarith
    have hB : 0 <= (2635571 / 500000000 : Real) * (1 - t) ^ 5
        + 5 * (441228147 / 17500000000 : Real) * t * (1 - t) ^ 4
        + 10 * (4992648149 / 122500000000 : Real) * t ^ 2 * (1 - t) ^ 3
        + 10 * (45126739257 / 857500000000 : Real) * t ^ 3 * (1 - t) ^ 2
        + 5 * (368820055539 / 6002500000000 : Real) * t ^ 4 * (1 - t)
        + (569293403211 / 8403500000000 : Real) * t ^ 5 := by
      exact research9_bernstein5_nonneg
        t (2635571 / 500000000 : Real) (441228147 / 17500000000 : Real) (4992648149 / 122500000000 : Real) (45126739257 / 857500000000 : Real) (368820055539 / 6002500000000 : Real) (569293403211 / 8403500000000 : Real) ht0 ht1
        (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    have hid : research9MonotonicityP c + (161 / 5000 : Real) =
        (2635571 / 500000000 : Real) * (1 - t) ^ 5
        + 5 * (441228147 / 17500000000 : Real) * t * (1 - t) ^ 4
        + 10 * (4992648149 / 122500000000 : Real) * t ^ 2 * (1 - t) ^ 3
        + 10 * (45126739257 / 857500000000 : Real) * t ^ 3 * (1 - t) ^ 2
        + 5 * (368820055539 / 6002500000000 : Real) * t ^ 4 * (1 - t)
        + (569293403211 / 8403500000000 : Real) * t ^ 5 := by
      dsimp [t, research9MonotonicityP]
      ring
    linarith
  ·
    by_cases h1 : c <= (-5 / 7 : Real)
    ·
      have hl : (-6 / 7 : Real) <= c := by
        exact le_of_lt (lt_of_not_ge h0)
      have hu : c <= (-5 / 7 : Real) := by
        exact h1
      let t : Real := 7 * (c - (-6 / 7 : Real))
      have ht0 : 0 <= t := by
        dsimp [t]
        linarith
      have ht1 : t <= 1 := by
        dsimp [t]
        linarith
      have hB : 0 <= (569293403211 / 8403500000000 : Real) * (1 - t) ^ 5
          + 5 * (3111193643337 / 42017500000000 : Real) * t * (1 - t) ^ 4
          + 10 * (3270116732721 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
          + 10 * (669126897923 / 8403500000000 : Real) * t ^ 3 * (1 - t) ^ 2
          + 5 * (3356387442467 / 42017500000000 : Real) * t ^ 4 * (1 - t)
          + (663561259113 / 8403500000000 : Real) * t ^ 5 := by
        exact research9_bernstein5_nonneg
          t (569293403211 / 8403500000000 : Real) (3111193643337 / 42017500000000 : Real) (3270116732721 / 42017500000000 : Real) (669126897923 / 8403500000000 : Real) (3356387442467 / 42017500000000 : Real) (663561259113 / 8403500000000 : Real) ht0 ht1
          (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num)
      have hid : research9MonotonicityP c + (161 / 5000 : Real) =
          (569293403211 / 8403500000000 : Real) * (1 - t) ^ 5
          + 5 * (3111193643337 / 42017500000000 : Real) * t * (1 - t) ^ 4
          + 10 * (3270116732721 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
          + 10 * (669126897923 / 8403500000000 : Real) * t ^ 3 * (1 - t) ^ 2
          + 5 * (3356387442467 / 42017500000000 : Real) * t ^ 4 * (1 - t)
          + (663561259113 / 8403500000000 : Real) * t ^ 5 := by
        dsimp [t, research9MonotonicityP]
        ring
      linarith
    ·
      by_cases h2 : c <= (-4 / 7 : Real)
      ·
        have hl : (-5 / 7 : Real) <= c := by
          exact le_of_lt (lt_of_not_ge h1)
        have hu : c <= (-4 / 7 : Real) := by
          exact h2
        let t : Real := 7 * (c - (-5 / 7 : Real))
        have ht0 : 0 <= t := by
          dsimp [t]
          linarith
        have ht1 : t <= 1 := by
          dsimp [t]
          linarith
        have hB : 0 <= (663561259113 / 8403500000000 : Real) * (1 - t) ^ 5
            + 5 * (3279225148663 / 42017500000000 : Real) * t * (1 - t) ^ 4
            + 10 * (3191309902007 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
            + 10 * (613898251977 / 8403500000000 : Real) * t ^ 3 * (1 - t) ^ 2
            + 5 * (117039604097 / 1680700000000 : Real) * t ^ 4 * (1 - t)
            + (554073067679 / 8403500000000 : Real) * t ^ 5 := by
          exact research9_bernstein5_nonneg
            t (663561259113 / 8403500000000 : Real) (3279225148663 / 42017500000000 : Real) (3191309902007 / 42017500000000 : Real) (613898251977 / 8403500000000 : Real) (117039604097 / 1680700000000 : Real) (554073067679 / 8403500000000 : Real) ht0 ht1
            (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)
        have hid : research9MonotonicityP c + (161 / 5000 : Real) =
            (663561259113 / 8403500000000 : Real) * (1 - t) ^ 5
            + 5 * (3279225148663 / 42017500000000 : Real) * t * (1 - t) ^ 4
            + 10 * (3191309902007 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
            + 10 * (613898251977 / 8403500000000 : Real) * t ^ 3 * (1 - t) ^ 2
            + 5 * (117039604097 / 1680700000000 : Real) * t ^ 4 * (1 - t)
            + (554073067679 / 8403500000000 : Real) * t ^ 5 := by
          dsimp [t, research9MonotonicityP]
          ring
        linarith
      ·
        by_cases h3 : c <= (-3 / 7 : Real)
        ·
          have hl : (-4 / 7 : Real) <= c := by
            exact le_of_lt (lt_of_not_ge h2)
          have hu : c <= (-3 / 7 : Real) := by
            exact h3
          let t : Real := 7 * (c - (-4 / 7 : Real))
          have ht0 : 0 <= t := by
            dsimp [t]
            linarith
          have ht1 : t <= 1 := by
            dsimp [t]
            linarith
          have hB : 0 <= (554073067679 / 8403500000000 : Real) * (1 - t) ^ 5
              + 5 * (522948114873 / 8403500000000 : Real) * t * (1 - t) ^ 4
              + 10 * (489398440753 / 8403500000000 : Real) * t ^ 2 * (1 - t) ^ 3
              + 10 * (2276679135363 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
              + 5 * (2110698306567 / 42017500000000 : Real) * t ^ 4 * (1 - t)
              + (78153301449 / 1680700000000 : Real) * t ^ 5 := by
            exact research9_bernstein5_nonneg
              t (554073067679 / 8403500000000 : Real) (522948114873 / 8403500000000 : Real) (489398440753 / 8403500000000 : Real) (2276679135363 / 42017500000000 : Real) (2110698306567 / 42017500000000 : Real) (78153301449 / 1680700000000 : Real) ht0 ht1
              (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          have hid : research9MonotonicityP c + (161 / 5000 : Real) =
              (554073067679 / 8403500000000 : Real) * (1 - t) ^ 5
              + 5 * (522948114873 / 8403500000000 : Real) * t * (1 - t) ^ 4
              + 10 * (489398440753 / 8403500000000 : Real) * t ^ 2 * (1 - t) ^ 3
              + 10 * (2276679135363 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
              + 5 * (2110698306567 / 42017500000000 : Real) * t ^ 4 * (1 - t)
              + (78153301449 / 1680700000000 : Real) * t ^ 5 := by
            dsimp [t, research9MonotonicityP]
            ring
          linarith
        ·
          by_cases h4 : c <= (-2 / 7 : Real)
          ·
            have hl : (-3 / 7 : Real) <= c := by
              exact le_of_lt (lt_of_not_ge h3)
            have hu : c <= (-2 / 7 : Real) := by
              exact h4
            let t : Real := 7 * (c - (-3 / 7 : Real))
            have ht0 : 0 <= t := by
              dsimp [t]
              linarith
            have ht1 : t <= 1 := by
              dsimp [t]
              linarith
            have hB : 0 <= (78153301449 / 1680700000000 : Real) * (1 - t) ^ 5
                + 5 * (1796966765883 / 42017500000000 : Real) * t * (1 - t) ^ 4
                + 10 * (329843210799 / 8403500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                + 10 * (1515363219409 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                + 5 * (1398076962413 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                + (259691943507 / 8403500000000 : Real) * t ^ 5 := by
              exact research9_bernstein5_nonneg
                t (78153301449 / 1680700000000 : Real) (1796966765883 / 42017500000000 : Real) (329843210799 / 8403500000000 : Real) (1515363219409 / 42017500000000 : Real) (1398076962413 / 42017500000000 : Real) (259691943507 / 8403500000000 : Real) ht0 ht1
                (by norm_num) (by norm_num) (by norm_num)
                (by norm_num) (by norm_num) (by norm_num)
            have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                (78153301449 / 1680700000000 : Real) * (1 - t) ^ 5
                + 5 * (1796966765883 / 42017500000000 : Real) * t * (1 - t) ^ 4
                + 10 * (329843210799 / 8403500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                + 10 * (1515363219409 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                + 5 * (1398076962413 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                + (259691943507 / 8403500000000 : Real) * t ^ 5 := by
              dsimp [t, research9MonotonicityP]
              ring
            linarith
          ·
            by_cases h5 : c <= (-1 / 7 : Real)
            ·
              have hl : (-2 / 7 : Real) <= c := by
                exact le_of_lt (lt_of_not_ge h4)
              have hu : c <= (-1 / 7 : Real) := by
                exact h5
              let t : Real := 7 * (c - (-2 / 7 : Real))
              have ht0 : 0 <= t := by
                dsimp [t]
                linarith
              have ht1 : t <= 1 := by
                dsimp [t]
                linarith
              have hB : 0 <= (259691943507 / 8403500000000 : Real) * (1 - t) ^ 5
                  + 5 * (1198842472657 / 42017500000000 : Real) * t * (1 - t) ^ 4
                  + 10 * (1116894239897 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                  + 10 * (1053717453783 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                  + 5 * (1008848283083 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                  + (196160896721 / 8403500000000 : Real) * t ^ 5 := by
                exact research9_bernstein5_nonneg
                  t (259691943507 / 8403500000000 : Real) (1198842472657 / 42017500000000 : Real) (1116894239897 / 42017500000000 : Real) (1053717453783 / 42017500000000 : Real) (1008848283083 / 42017500000000 : Real) (196160896721 / 8403500000000 : Real) ht0 ht1
                  (by norm_num) (by norm_num) (by norm_num)
                  (by norm_num) (by norm_num) (by norm_num)
              have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                  (259691943507 / 8403500000000 : Real) * (1 - t) ^ 5
                  + 5 * (1198842472657 / 42017500000000 : Real) * t * (1 - t) ^ 4
                  + 10 * (1116894239897 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                  + 10 * (1053717453783 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                  + 5 * (1008848283083 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                  + (196160896721 / 8403500000000 : Real) * t ^ 5 := by
                dsimp [t, research9MonotonicityP]
                ring
              linarith
            ·
              by_cases h6 : c <= (0 : Real)
              ·
                have hl : (-1 / 7 : Real) <= c := by
                  exact le_of_lt (lt_of_not_ge h5)
                have hu : c <= (0 : Real) := by
                  exact h6
                let t : Real := 7 * (c - (-1 / 7 : Real))
                have ht0 : 0 <= t := by
                  dsimp [t]
                  linarith
                have ht1 : t <= 1 := by
                  dsimp [t]
                  linarith
                have hB : 0 <= (196160896721 / 8403500000000 : Real) * (1 - t) ^ 5
                    + 5 * (136108669161 / 6002500000000 : Real) * t * (1 - t) ^ 4
                    + 10 * (19215148079 / 857500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                    + 10 * (551409303 / 24500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                    + 5 * (400930497 / 17500000000 : Real) * t ^ 4 * (1 - t)
                    + (11774529 / 500000000 : Real) * t ^ 5 := by
                  exact research9_bernstein5_nonneg
                    t (196160896721 / 8403500000000 : Real) (136108669161 / 6002500000000 : Real) (19215148079 / 857500000000 : Real) (551409303 / 24500000000 : Real) (400930497 / 17500000000 : Real) (11774529 / 500000000 : Real) ht0 ht1
                    (by norm_num) (by norm_num) (by norm_num)
                    (by norm_num) (by norm_num) (by norm_num)
                have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                    (196160896721 / 8403500000000 : Real) * (1 - t) ^ 5
                    + 5 * (136108669161 / 6002500000000 : Real) * t * (1 - t) ^ 4
                    + 10 * (19215148079 / 857500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                    + 10 * (551409303 / 24500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                    + 5 * (400930497 / 17500000000 : Real) * t ^ 4 * (1 - t)
                    + (11774529 / 500000000 : Real) * t ^ 5 := by
                  dsimp [t, research9MonotonicityP]
                  ring
                linarith
              ·
                by_cases h7 : c <= (1 / 7 : Real)
                ·
                  have hl : (0 : Real) <= c := by
                    exact le_of_lt (lt_of_not_ge h6)
                  have hu : c <= (1 / 7 : Real) := by
                    exact h7
                  let t : Real := 7 * (c - (0 : Real))
                  have ht0 : 0 <= t := by
                    dsimp [t]
                    linarith
                  have ht1 : t <= 1 := by
                    dsimp [t]
                    linarith
                  have hB : 0 <= (11774529 / 500000000 : Real) * (1 - t) ^ 5
                      + 5 * (423286533 / 17500000000 : Real) * t * (1 - t) ^ 4
                      + 10 * (3070031019 / 122500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                      + 10 * (4476042239 / 171500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                      + 5 * (1307083789 / 48020000000 : Real) * t ^ 4 * (1 - t)
                      + (238172011029 / 8403500000000 : Real) * t ^ 5 := by
                    exact research9_bernstein5_nonneg
                      t (11774529 / 500000000 : Real) (423286533 / 17500000000 : Real) (3070031019 / 122500000000 : Real) (4476042239 / 171500000000 : Real) (1307083789 / 48020000000 : Real) (238172011029 / 8403500000000 : Real) ht0 ht1
                      (by norm_num) (by norm_num) (by norm_num)
                      (by norm_num) (by norm_num) (by norm_num)
                  have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                      (11774529 / 500000000 : Real) * (1 - t) ^ 5
                      + 5 * (423286533 / 17500000000 : Real) * t * (1 - t) ^ 4
                      + 10 * (3070031019 / 122500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                      + 10 * (4476042239 / 171500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                      + 5 * (1307083789 / 48020000000 : Real) * t ^ 4 * (1 - t)
                      + (238172011029 / 8403500000000 : Real) * t ^ 5 := by
                    dsimp [t, research9MonotonicityP]
                    ring
                  linarith
                ·
                  by_cases h8 : c <= (2 / 7 : Real)
                  ·
                    have hl : (1 / 7 : Real) <= c := by
                      exact le_of_lt (lt_of_not_ge h7)
                    have hu : c <= (2 / 7 : Real) := by
                      exact h8
                    let t : Real := 7 * (c - (1 / 7 : Real))
                    have ht0 : 0 <= t := by
                      dsimp [t]
                      linarith
                    have ht1 : t <= 1 := by
                      dsimp [t]
                      linarith
                    have hB : 0 <= (238172011029 / 8403500000000 : Real) * (1 - t) ^ 5
                        + 5 * (247604358983 / 8403500000000 : Real) * t * (1 - t) ^ 4
                        + 10 * (257055461527 / 8403500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                        + 10 * (1329262108473 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                        + 5 * (1366689005237 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                        + (55795838047 / 1680700000000 : Real) * t ^ 5 := by
                      exact research9_bernstein5_nonneg
                        t (238172011029 / 8403500000000 : Real) (247604358983 / 8403500000000 : Real) (257055461527 / 8403500000000 : Real) (1329262108473 / 42017500000000 : Real) (1366689005237 / 42017500000000 : Real) (55795838047 / 1680700000000 : Real) ht0 ht1
                        (by norm_num) (by norm_num) (by norm_num)
                        (by norm_num) (by norm_num) (by norm_num)
                    have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                        (238172011029 / 8403500000000 : Real) * (1 - t) ^ 5
                        + 5 * (247604358983 / 8403500000000 : Real) * t * (1 - t) ^ 4
                        + 10 * (257055461527 / 8403500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                        + 10 * (1329262108473 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                        + 5 * (1366689005237 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                        + (55795838047 / 1680700000000 : Real) * t ^ 5 := by
                      dsimp [t, research9MonotonicityP]
                      ring
                    linarith
                  ·
                    by_cases h9 : c <= (3 / 7 : Real)
                    ·
                      have hl : (2 / 7 : Real) <= c := by
                        exact le_of_lt (lt_of_not_ge h8)
                      have hu : c <= (3 / 7 : Real) := by
                        exact h9
                      let t : Real := 7 * (c - (2 / 7 : Real))
                      have ht0 : 0 <= t := by
                        dsimp [t]
                        linarith
                      have ht1 : t <= 1 := by
                        dsimp [t]
                        linarith
                      have hB : 0 <= (55795838047 / 1680700000000 : Real) * (1 - t) ^ 5
                          + 5 * (1423102897113 / 42017500000000 : Real) * t * (1 - t) ^ 4
                          + 10 * (57683595689 / 1680700000000 : Real) * t ^ 2 * (1 - t) ^ 3
                          + 10 * (1449194889759 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                          + 5 * (1442380988403 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                          + (284156857017 / 8403500000000 : Real) * t ^ 5 := by
                        exact research9_bernstein5_nonneg
                          t (55795838047 / 1680700000000 : Real) (1423102897113 / 42017500000000 : Real) (57683595689 / 1680700000000 : Real) (1449194889759 / 42017500000000 : Real) (1442380988403 / 42017500000000 : Real) (284156857017 / 8403500000000 : Real) ht0 ht1
                          (by norm_num) (by norm_num) (by norm_num)
                          (by norm_num) (by norm_num) (by norm_num)
                      have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                          (55795838047 / 1680700000000 : Real) * (1 - t) ^ 5
                          + 5 * (1423102897113 / 42017500000000 : Real) * t * (1 - t) ^ 4
                          + 10 * (57683595689 / 1680700000000 : Real) * t ^ 2 * (1 - t) ^ 3
                          + 10 * (1449194889759 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                          + 5 * (1442380988403 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                          + (284156857017 / 8403500000000 : Real) * t ^ 5 := by
                        dsimp [t, research9MonotonicityP]
                        ring
                      linarith
                    ·
                      by_cases h10 : c <= (4 / 7 : Real)
                      ·
                        have hl : (3 / 7 : Real) <= c := by
                          exact le_of_lt (lt_of_not_ge h9)
                        have hu : c <= (4 / 7 : Real) := by
                          exact h10
                        let t : Real := 7 * (c - (3 / 7 : Real))
                        have ht0 : 0 <= t := by
                          dsimp [t]
                          linarith
                        have ht1 : t <= 1 := by
                          dsimp [t]
                          linarith
                        have hB : 0 <= (284156857017 / 8403500000000 : Real) * (1 - t) ^ 5
                            + 5 * (1399187581767 / 42017500000000 : Real) * t * (1 - t) ^ 4
                            + 10 * (1362808076487 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                            + 10 * (1310781866173 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                            + 5 * (1243418045993 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                            + (232549312431 / 8403500000000 : Real) * t ^ 5 := by
                          exact research9_bernstein5_nonneg
                            t (284156857017 / 8403500000000 : Real) (1399187581767 / 42017500000000 : Real) (1362808076487 / 42017500000000 : Real) (1310781866173 / 42017500000000 : Real) (1243418045993 / 42017500000000 : Real) (232549312431 / 8403500000000 : Real) ht0 ht1
                            (by norm_num) (by norm_num) (by norm_num)
                            (by norm_num) (by norm_num) (by norm_num)
                        have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                            (284156857017 / 8403500000000 : Real) * (1 - t) ^ 5
                            + 5 * (1399187581767 / 42017500000000 : Real) * t * (1 - t) ^ 4
                            + 10 * (1362808076487 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                            + 10 * (1310781866173 / 42017500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                            + 5 * (1243418045993 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                            + (232549312431 / 8403500000000 : Real) * t ^ 5 := by
                          dsimp [t, research9MonotonicityP]
                          ring
                        linarith
                      ·
                        by_cases h11 : c <= (5 / 7 : Real)
                        ·
                          have hl : (4 / 7 : Real) <= c := by
                            exact le_of_lt (lt_of_not_ge h10)
                          have hu : c <= (5 / 7 : Real) := by
                            exact h11
                          let t : Real := 7 * (c - (4 / 7 : Real))
                          have ht0 : 0 <= t := by
                            dsimp [t]
                            linarith
                          have ht1 : t <= 1 := by
                            dsimp [t]
                            linarith
                          have hB : 0 <= (232549312431 / 8403500000000 : Real) * (1 - t) ^ 5
                              + 5 * (1082075078317 / 42017500000000 : Real) * t * (1 - t) ^ 4
                              + 10 * (988095930821 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                              + 10 * (7062712527 / 336140000000 : Real) * t ^ 3 * (1 - t) ^ 2
                              + 5 * (770055280727 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                              + (131152815293 / 8403500000000 : Real) * t ^ 5 := by
                            exact research9_bernstein5_nonneg
                              t (232549312431 / 8403500000000 : Real) (1082075078317 / 42017500000000 : Real) (988095930821 / 42017500000000 : Real) (7062712527 / 336140000000 : Real) (770055280727 / 42017500000000 : Real) (131152815293 / 8403500000000 : Real) ht0 ht1
                              (by norm_num) (by norm_num) (by norm_num)
                              (by norm_num) (by norm_num) (by norm_num)
                          have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                              (232549312431 / 8403500000000 : Real) * (1 - t) ^ 5
                              + 5 * (1082075078317 / 42017500000000 : Real) * t * (1 - t) ^ 4
                              + 10 * (988095930821 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                              + 10 * (7062712527 / 336140000000 : Real) * t ^ 3 * (1 - t) ^ 2
                              + 5 * (770055280727 / 42017500000000 : Real) * t ^ 4 * (1 - t)
                              + (131152815293 / 8403500000000 : Real) * t ^ 5 := by
                            dsimp [t, research9MonotonicityP]
                            ring
                          linarith
                        ·
                          by_cases h12 : c <= (6 / 7 : Real)
                          ·
                            have hl : (5 / 7 : Real) <= c := by
                              exact le_of_lt (lt_of_not_ge h11)
                            have hu : c <= (6 / 7 : Real) := by
                              exact h12
                            let t : Real := 7 * (c - (5 / 7 : Real))
                            have ht0 : 0 <= t := by
                              dsimp [t]
                              linarith
                            have ht1 : t <= 1 := by
                              dsimp [t]
                              linarith
                            have hB : 0 <= (131152815293 / 8403500000000 : Real) * (1 - t) ^ 5
                                + 5 * (541472872203 / 42017500000000 : Real) * t * (1 - t) ^ 4
                                + 10 * (425674248827 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                                + 10 * (12575508297 / 1680700000000 : Real) * t ^ 3 * (1 - t) ^ 2
                                + 5 * (8636058117 / 1680700000000 : Real) * t ^ 4 * (1 - t)
                                + (28264049379 / 8403500000000 : Real) * t ^ 5 := by
                              exact research9_bernstein5_nonneg
                                t (131152815293 / 8403500000000 : Real) (541472872203 / 42017500000000 : Real) (425674248827 / 42017500000000 : Real) (12575508297 / 1680700000000 : Real) (8636058117 / 1680700000000 : Real) (28264049379 / 8403500000000 : Real) ht0 ht1
                                (by norm_num) (by norm_num) (by norm_num)
                                (by norm_num) (by norm_num) (by norm_num)
                            have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                                (131152815293 / 8403500000000 : Real) * (1 - t) ^ 5
                                + 5 * (541472872203 / 42017500000000 : Real) * t * (1 - t) ^ 4
                                + 10 * (425674248827 / 42017500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                                + 10 * (12575508297 / 1680700000000 : Real) * t ^ 3 * (1 - t) ^ 2
                                + 5 * (8636058117 / 1680700000000 : Real) * t ^ 4 * (1 - t)
                                + (28264049379 / 8403500000000 : Real) * t ^ 5 := by
                              dsimp [t, research9MonotonicityP]
                              ring
                            linarith
                          ·
                            have hl : (6 / 7 : Real) <= c := by
                              exact le_of_lt (lt_of_not_ge h12)
                            have hu : c <= (1 : Real) := by
                              exact hcU
                            let t : Real := 7 * (c - (6 / 7 : Real))
                            have ht0 : 0 <= t := by
                              dsimp [t]
                              linarith
                            have ht1 : t <= 1 := by
                              dsimp [t]
                              linarith
                            have hB : 0 <= (28264049379 / 8403500000000 : Real) * (1 - t) ^ 5
                                + 5 * (1906829739 / 1200500000000 : Real) * t * (1 - t) ^ 4
                                + 10 * (65562789 / 171500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                                + 10 * (1156081 / 122500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                                + 5 * (14019707 / 17500000000 : Real) * t ^ 4 * (1 - t)
                                + (507 / 160000 : Real) * t ^ 5 := by
                              exact research9_bernstein5_nonneg
                                t (28264049379 / 8403500000000 : Real) (1906829739 / 1200500000000 : Real) (65562789 / 171500000000 : Real) (1156081 / 122500000000 : Real) (14019707 / 17500000000 : Real) (507 / 160000 : Real) ht0 ht1
                                (by norm_num) (by norm_num) (by norm_num)
                                (by norm_num) (by norm_num) (by norm_num)
                            have hid : research9MonotonicityP c + (161 / 5000 : Real) =
                                (28264049379 / 8403500000000 : Real) * (1 - t) ^ 5
                                + 5 * (1906829739 / 1200500000000 : Real) * t * (1 - t) ^ 4
                                + 10 * (65562789 / 171500000000 : Real) * t ^ 2 * (1 - t) ^ 3
                                + 10 * (1156081 / 122500000000 : Real) * t ^ 3 * (1 - t) ^ 2
                                + 5 * (14019707 / 17500000000 : Real) * t ^ 4 * (1 - t)
                                + (507 / 160000 : Real) * t ^ 5 := by
                              dsimp [t, research9MonotonicityP]
                              ring
                            linarith


/-- Exact derivative expression for the pinned seven-term profile. -/
def research9WindowDerivative (s : Real) : Real :=
    -Real.sqrt 2 * Real.sin (Real.sqrt 2 * s)
    - (3322500 / 1000000000 : Real) *
        (2 * Real.pi) * Real.sin ((2 * Real.pi) * s)
    + (7609135 / 1000000000 : Real) *
        (4 * Real.pi) * Real.sin ((4 * Real.pi) * s)
    - (1190194 / 1000000000 : Real) *
        (6 * Real.pi) * Real.sin ((6 * Real.pi) * s)
    + (731476 / 1000000000 : Real) *
        (8 * Real.pi) * Real.sin ((8 * Real.pi) * s)
    + (1680572 / 1000000000 : Real) *
        (10 * Real.pi) * Real.sin ((10 * Real.pi) * s)
    - (1141360 / 1000000000 : Real) *
        (12 * Real.pi) * Real.sin ((12 * Real.pi) * s)

/-- The displayed expression above is the actual derivative of
`research9Window`. -/
theorem research9Window_hasDerivAt (s : Real) :
    HasDerivAt research9Window (research9WindowDerivative s) s := by
  have hcos :
      forall k : Real,
        HasDerivAt
          (fun x : Real => Real.cos (k * x))
          (-Real.sin (k * s) * k) s := by
    intro k
    simpa using ((hasDerivAt_id s).const_mul k).cos


  have h0 := hcos (Real.sqrt 2)

  have h1 :=
    (hcos (2 * Real.pi)).const_mul
      (3322500 / 1000000000 : Real)

  have h2 :=
    (hcos (4 * Real.pi)).const_mul
      (7609135 / 1000000000 : Real)

  have h3 :=
    (hcos (6 * Real.pi)).const_mul
      (1190194 / 1000000000 : Real)

  have h4 :=
    (hcos (8 * Real.pi)).const_mul
      (731476 / 1000000000 : Real)

  have h5 :=
    (hcos (10 * Real.pi)).const_mul
      (1680572 / 1000000000 : Real)

  have h6 :=
    (hcos (12 * Real.pi)).const_mul
      (1141360 / 1000000000 : Real)

  have h01 := h0.add h1
  have h012 := h01.sub h2
  have h0123 := h012.add h3
  have h01234 := h0123.sub h4
  have h012345 := h01234.sub h5
  have hfinal := h012345.add h6

  unfold research9Window
  apply hfinal.congr_deriv
  unfold research9WindowDerivative
  ring

/-- Pointwise derivative identity. -/
theorem research9Window_deriv (s : Real) :
    deriv research9Window s = research9WindowDerivative s :=
  (research9Window_hasDerivAt s).deriv


/-- Exact Chebyshev factorization of the six Fourier perturbation terms. -/
theorem research9_perturbation_sine_factor (x : Real) :
    (3322500 / 1000000000 : Real) * Real.sin x
      - (2 * (7609135 / 1000000000 : Real)) * Real.sin (2 * x)
      + (3 * (1190194 / 1000000000 : Real)) * Real.sin (3 * x)
      - (4 * (731476 / 1000000000 : Real)) * Real.sin (4 * x)
      - (5 * (1680572 / 1000000000 : Real)) * Real.sin (5 * x)
      + (6 * (1141360 / 1000000000 : Real)) * Real.sin (6 * x)
      =
    Real.sin x * research9MonotonicityP (Real.cos x) := by

  let c : Real := Real.cos x

  have hU1 :
      (Polynomial.Chebyshev.U Real (1 : Int)).eval c =
        2 * c := by
    dsimp [c]
    norm_num [Polynomial.Chebyshev.U]

  have hU2 :
      (Polynomial.Chebyshev.U Real (2 : Int)).eval c =
        4 * c^2 - 1 := by
    rw [Polynomial.Chebyshev.U_two]
    simp

  have hU3 :
      (Polynomial.Chebyshev.U Real (3 : Int)).eval c =
        8 * c^3 - 4 * c := by
    have hrec :=
      Polynomial.Chebyshev.U_add_two Real (1 : Int)
    norm_num at hrec
    rw [hrec]
    rw [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
    rw [hU2]
    ring

  have hU4 :
      (Polynomial.Chebyshev.U Real (4 : Int)).eval c =
        16 * c^4 - 12 * c^2 + 1 := by
    have hrec :=
      Polynomial.Chebyshev.U_add_two Real (2 : Int)
    norm_num at hrec
    rw [hrec]
    rw [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
    rw [hU3, hU2]
    ring

  have hU5 :
      (Polynomial.Chebyshev.U Real (5 : Int)).eval c =
        32 * c^5 - 32 * c^3 + 6 * c := by
    have hrec :=
      Polynomial.Chebyshev.U_add_two Real (3 : Int)
    norm_num at hrec
    rw [hrec]
    rw [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
    rw [hU4, hU3]
    ring


  have hs2 :
      Real.sin (2 * x) = (2 * c) * Real.sin x := by
    have h := Polynomial.Chebyshev.U_real_cos x (1 : Int)
    rw [show Real.cos x = c by rfl] at h
    rw [hU1] at h
    norm_num at h
    exact h.symm

  have hs3 :
      Real.sin (3 * x) = (4 * c^2 - 1) * Real.sin x := by
    have h := Polynomial.Chebyshev.U_real_cos x (2 : Int)
    rw [show Real.cos x = c by rfl] at h
    rw [hU2] at h
    norm_num at h
    exact h.symm

  have hs4 :
      Real.sin (4 * x) = (8 * c^3 - 4 * c) * Real.sin x := by
    have h := Polynomial.Chebyshev.U_real_cos x (3 : Int)
    rw [show Real.cos x = c by rfl] at h
    rw [hU3] at h
    norm_num at h
    exact h.symm

  have hs5 :
      Real.sin (5 * x) =
        (16 * c^4 - 12 * c^2 + 1) * Real.sin x := by
    have h := Polynomial.Chebyshev.U_real_cos x (4 : Int)
    rw [show Real.cos x = c by rfl] at h
    rw [hU4] at h
    norm_num at h
    exact h.symm

  have hs6 :
      Real.sin (6 * x) =
        (32 * c^5 - 32 * c^3 + 6 * c) * Real.sin x := by
    have h := Polynomial.Chebyshev.U_real_cos x (5 : Int)
    rw [show Real.cos x = c by rfl] at h
    rw [hU5] at h
    norm_num at h
    exact h.symm

  rw [hs2, hs3, hs4, hs5, hs6]
  dsimp [c]
  unfold research9MonotonicityP
  ring


/-- Exact factorization of the negative derivative into the main mode
and the certified Chebyshev perturbation polynomial. -/
theorem research9WindowDerivative_neg_factor (s : Real) :
    -research9WindowDerivative s =
      Real.sqrt 2 * Real.sin (Real.sqrt 2 * s)
        + 2 * Real.pi *
            (Real.sin ((2 * Real.pi) * s) *
              research9MonotonicityP
                (Real.cos ((2 * Real.pi) * s))) := by
  have h :=
    research9_perturbation_sine_factor ((2 * Real.pi) * s)

  unfold research9WindowDerivative
  ring_nf at h 

  linear_combination (norm := ring_nf) (2 * Real.pi) * h


/-- Jordan lower bound for the main cosine mode on the half-window. -/
theorem research9_main_mode_lower
    {s : Real}
    (hs0 : 0 <= s)
    (hs1 : s <= 1 / 2) :
    4 * s / Real.pi <=
      Real.sqrt 2 * Real.sin (Real.sqrt 2 * s) := by
  have hsqrt0 : 0 <= Real.sqrt 2 := Real.sqrt_nonneg 2

  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : Real) := by
    exact Real.sq_sqrt (by norm_num)

  have hsqrt_le_two : Real.sqrt 2 <= 2 := by
    nlinarith

  have hx0 : 0 <= Real.sqrt 2 * s := by
    exact mul_nonneg hsqrt0 hs0

  have hx_le_one : Real.sqrt 2 * s <= 1 := by
    calc
      Real.sqrt 2 * s <= 2 * s :=
        mul_le_mul_of_nonneg_right hsqrt_le_two hs0
      _ <= 1 := by linarith

  have hone_le_pi_half : (1 : Real) <= Real.pi / 2 := by
    linarith [Real.pi_gt_three]

  have hxpi : Real.sqrt 2 * s <= Real.pi / 2 :=
    hx_le_one.trans hone_le_pi_half

  have hjordan :
      2 / Real.pi * (Real.sqrt 2 * s) <=
        Real.sin (Real.sqrt 2 * s) :=
    Real.mul_le_sin hx0 hxpi

  have hjordan_mul :
      Real.sqrt 2 *
          (2 / Real.pi * (Real.sqrt 2 * s))
        <=
      Real.sqrt 2 *
          Real.sin (Real.sqrt 2 * s) :=
    mul_le_mul_of_nonneg_left hjordan hsqrt0

  have hsqrt_mul :
      Real.sqrt 2 * Real.sqrt 2 = (2 : Real) := by
    nlinarith [hsqrt_sq]

  have halg :
      Real.sqrt 2 *
          (2 / Real.pi * (Real.sqrt 2 * s))
        =
      4 * s / Real.pi := by
    calc
      Real.sqrt 2 *
          (2 / Real.pi * (Real.sqrt 2 * s))
          =
        (Real.sqrt 2 * Real.sqrt 2) *
          (2 * s / Real.pi) := by ring
      _ = 2 * (2 * s / Real.pi) := by rw [hsqrt_mul]
      _ = 4 * s / Real.pi := by ring

  rw [halg] at hjordan_mul
  exact hjordan_mul


/-- Lower bound for the six-mode perturbation on the half-window. -/
theorem research9_perturbation_lower
    {s : Real}
    (hs0 : 0 <= s)
    (hs1 : s <= 1 / 2) :
    -4 * Real.pi^2 * (161 / 5000 : Real) * s <=
      2 * Real.pi *
        (Real.sin ((2 * Real.pi) * s) *
          research9MonotonicityP
            (Real.cos ((2 * Real.pi) * s))) := by

  let x : Real := (2 * Real.pi) * s
  let q : Real := 161 / 5000

  have hx0 : 0 <= x := by
    dsimp [x]
    exact mul_nonneg (by positivity) hs0

  have hxpi : x <= Real.pi := by
    dsimp [x]
    calc
      (2 * Real.pi) * s <=
          (2 * Real.pi) * (1 / 2 : Real) :=
        mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = Real.pi := by ring

  have hsin0 : 0 <= Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi

  have hcos := Real.cos_mem_Icc x

  have hP :
      -q <= research9MonotonicityP (Real.cos x) := by
    have h :=
      research9MonotonicityP_ge hcos.1 hcos.2
    dsimp [q]
    norm_num at h 
    exact h

  have hPsin :
      (-q) * Real.sin x <=
        research9MonotonicityP (Real.cos x) * Real.sin x :=
    mul_le_mul_of_nonneg_right hP hsin0

  have hpi0 : 0 <= 2 * Real.pi := by
    positivity

  have hPterm :
      (2 * Real.pi) * ((-q) * Real.sin x) <=
        (2 * Real.pi) *
          (research9MonotonicityP (Real.cos x) * Real.sin x) :=
    mul_le_mul_of_nonneg_left hPsin hpi0

  have hsin_le : Real.sin x <= x :=
    Real.sin_le hx0

  have hq0 : 0 <= q := by
    dsimp [q]
    norm_num

  have hqsin :
      q * Real.sin x <= q * x :=
    mul_le_mul_of_nonneg_left hsin_le hq0

  have hneg :
      -(q * x) <= -(q * Real.sin x) :=
    neg_le_neg hqsin

  have hnegterm :
      (2 * Real.pi) * (-(q * x)) <=
        (2 * Real.pi) * (-(q * Real.sin x)) :=
    mul_le_mul_of_nonneg_left hneg hpi0

  calc
    -4 * Real.pi^2 * (161 / 5000 : Real) * s
        =
      (2 * Real.pi) * (-(q * x)) := by
        dsimp [q, x]
        ring
    _ <= (2 * Real.pi) * (-(q * Real.sin x)) :=
      hnegterm
    _ =
      (2 * Real.pi) * ((-q) * Real.sin x) := by
        ring
    _ <=
      (2 * Real.pi) *
        (research9MonotonicityP (Real.cos x) * Real.sin x) :=
      hPterm
    _ =
      2 * Real.pi *
        (Real.sin ((2 * Real.pi) * s) *
          research9MonotonicityP
            (Real.cos ((2 * Real.pi) * s))) := by
        dsimp [x]
        ring


/-- The Bernstein error constant is small enough for the derivative argument. -/
theorem research9_q_pi_cube_lt_one :
    (161 / 5000 : Real) * Real.pi^3 < 1 := by
  have hpi :
      Real.pi < (3.1416 : Real) :=
    Real.pi_lt_d4

  have hdiff :
      0 < (3.1416 : Real) - Real.pi := by
    exact sub_pos.mpr hpi

  have hquad :
      0 <
        (3.1416 : Real)^2
          + (3.1416 : Real) * Real.pi
          + Real.pi^2 := by
    positivity

  have hfactor :
      0 <
        ((3.1416 : Real) - Real.pi) *
          ((3.1416 : Real)^2
            + (3.1416 : Real) * Real.pi
            + Real.pi^2) := by
    exact mul_pos hdiff hquad

  have hpi3 :
      Real.pi^3 < (3.1416 : Real)^3 := by
    nlinarith [hfactor]

  have hq :
      (0 : Real) < 161 / 5000 := by
    norm_num

  have hmul :
      (161 / 5000 : Real) * Real.pi^3 <
        (161 / 5000 : Real) * (3.1416 : Real)^3 :=
    mul_lt_mul_of_pos_left hpi3 hq

  have hrat :
      (161 / 5000 : Real) * (3.1416 : Real)^3 < 1 := by
    norm_num

  exact hmul.trans hrat


/-- The exact derivative expression is nonpositive on the positive half-window. -/
theorem research9WindowDerivative_nonpos
    {s : Real}
    (hs0 : 0 <= s)
    (hs1 : s <= 1 / 2) :
    research9WindowDerivative s <= 0 := by

  have hmain :=
    research9_main_mode_lower hs0 hs1

  have hpert :=
    research9_perturbation_lower hs0 hs1

  have hfactor :=
    research9WindowDerivative_neg_factor s

  have hcoef :
      0 <
        1 - (161 / 5000 : Real) * Real.pi^3 := by
    exact sub_pos.mpr research9_q_pi_cube_lt_one

  have hbase :
      0 <= 4 * s / Real.pi := by
    exact div_nonneg
      (mul_nonneg (by norm_num) hs0)
      Real.pi_pos.le

  have hprod :
      0 <=
        (4 * s / Real.pi) *
          (1 - (161 / 5000 : Real) * Real.pi^3) := by
    exact mul_nonneg hbase hcoef.le

  have halg :
      (4 * s / Real.pi) *
          (1 - (161 / 5000 : Real) * Real.pi^3)
        =
      4 * s / Real.pi
        - 4 * Real.pi^2 * (161 / 5000 : Real) * s := by
    field_simp [Real.pi_ne_zero]

  have hlower :
      0 <=
        4 * s / Real.pi
          - 4 * Real.pi^2 * (161 / 5000 : Real) * s := by
    rw [halg] at hprod
    exact hprod

  have hsum :
      4 * s / Real.pi
          - 4 * Real.pi^2 * (161 / 5000 : Real) * s
        <=
      Real.sqrt 2 * Real.sin (Real.sqrt 2 * s)
        + 2 * Real.pi *
            (Real.sin ((2 * Real.pi) * s) *
              research9MonotonicityP
                (Real.cos ((2 * Real.pi) * s))) := by
    linarith

  have hneg :
      0 <= -research9WindowDerivative s := by
    rw [hfactor]
    exact hlower.trans hsum

  linarith

/-- The actual derivative of the research window is nonpositive on [0, 1/2]. -/
theorem research9Window_deriv_nonpos
    {s : Real}
    (hs0 : 0 <= s)
    (hs1 : s <= 1 / 2) :
    deriv research9Window s <= 0 := by
  rw [research9Window_deriv]
  exact research9WindowDerivative_nonpos hs0 hs1


/-- The pinned research window is antitone on the positive half-window. -/
theorem research9Window_antitoneOn :
    AntitoneOn research9Window (Set.Icc (0 : Real) (1 / 2)) := by

  have hcont :
      ContinuousOn research9Window
        (Set.Icc (0 : Real) (1 / 2)) := by
    have hc : Continuous research9Window := by
      unfold research9Window
      fun_prop
    exact hc.continuousOn

  have hdiff :
      DifferentiableOn Real research9Window
        (interior (Set.Icc (0 : Real) (1 / 2))) := by
    intro z hz
    exact
      (research9Window_hasDerivAt z).differentiableAt.differentiableWithinAt

  exact
    antitoneOn_of_deriv_nonpos
      (convex_Icc (0 : Real) (1 / 2))
      hcont
      hdiff
      (fun z hz => by
        rw [interior_Icc] at hz
        exact research9Window_deriv_nonpos hz.1.le hz.2.le)

end HurtadoZeta23
