import HurtadoZeta23.V26RationalBall
import HurtadoZeta23.V26LocalClosedForms
import HurtadoZeta23.V21KernelRootBrackets
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- A sine enclosure obtained from endpoint Taylor bounds and monotonicity on
    the small phase interval used by every final-cell certificate. -/
lemma v26_sin_ball_between {lo t hi : ℝ}
    (hlo0 : 0 ≤ lo) (hlot : lo ≤ t) (hthi : t ≤ hi) (hhi1 : hi ≤ 1) :
    v26Ball (Real.sin t)
      ((v21RootSinLower7 lo + v21RootSinUpper9 hi) / 2)
      ((v21RootSinUpper9 hi - v21RootSinLower7 lo) / 2) := by
  have ht0 : 0 ≤ t := hlo0.trans hlot
  have hhi0 : 0 ≤ hi := ht0.trans hthi
  have hlo1 : lo ≤ 1 := hlot.trans (hthi.trans hhi1)
  have hone : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hloMem : lo ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos]
    · exact hlo1.trans hone
  have htMem : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos]
    · exact hthi.trans (hhi1.trans hone)
  have hhiMem : hi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos]
    · exact hhi1.trans hone
  have hsinLo : v21RootSinLower7 lo ≤ Real.sin lo := by
    simpa [v21RootSinLower7] using v21_sin_lower7 hlo0 hlo1
  have hsinHi : Real.sin hi ≤ v21RootSinUpper9 hi := by
    simpa [v21RootSinUpper9] using v21_sin_upper9 hhi0 hhi1
  apply v26_ball_of_bounds
  · exact hsinLo.trans (Real.monotoneOn_sin hloMem htMem hlot)
  · exact (Real.monotoneOn_sin htMem hhiMem hthi).trans hsinHi

/-- Cosine enclosure on a nonnegative phase interval. -/
lemma v26_cos_ball_between {lo t hi : ℝ}
    (hlo0 : 0 ≤ lo) (hlot : lo ≤ t) (hthi : t ≤ hi) (hhi1 : hi ≤ 1) :
    v26Ball (Real.cos t)
      ((v21RootCosLower10 hi + v21RootCosUpper8 lo) / 2)
      ((v21RootCosUpper8 lo - v21RootCosLower10 hi) / 2) := by
  have ht0 : 0 ≤ t := hlo0.trans hlot
  have hhi0 : 0 ≤ hi := ht0.trans hthi
  have hlo1 : lo ≤ 1 := hlot.trans (hthi.trans hhi1)
  have hone : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hloMem : lo ∈ Set.Icc 0 Real.pi := ⟨hlo0, hlo1.trans hone⟩
  have htMem : t ∈ Set.Icc 0 Real.pi :=
    ⟨ht0, hthi.trans (hhi1.trans hone)⟩
  have hhiMem : hi ∈ Set.Icc 0 Real.pi := ⟨hhi0, hhi1.trans hone⟩
  have hcosLo : v21RootCosLower10 hi ≤ Real.cos hi := by
    simpa [v21RootCosLower10] using v21_cos_lower10 hhi0 hhi1
  have hcosHi : Real.cos lo ≤ v21RootCosUpper8 lo := by
    simpa [v21RootCosUpper8] using v21_cos_upper8 hlo0 hlo1
  apply v26_ball_of_bounds
  · exact hcosLo.trans (Real.antitoneOn_cos htMem hhiMem hthi)
  · exact (Real.antitoneOn_cos hloMem htMem hlot).trans hcosHi

/-- Sine enclosure on a final subcell lying to the right of its integer phase
    centre. -/
lemma v26_sin_local_right_ball {N : ℕ} {L U x : ℝ}
    (hNL : (N : ℝ) ≤ L) (hL : L ≤ x) (hU : x ≤ U)
    (hphase : v21RootPiU * (U - (N : ℝ)) ≤ 1) :
    v26Ball (Real.sin (v26LocalPhase N x))
      ((v21RootSinLower7 (v21RootPiL * (L - (N : ℝ))) +
          v21RootSinUpper9 (v21RootPiU * (U - (N : ℝ)))) / 2)
      ((v21RootSinUpper9 (v21RootPiU * (U - (N : ℝ))) -
          v21RootSinLower7 (v21RootPiL * (L - (N : ℝ)))) / 2) := by
  have hpiL : v21RootPiL ≤ Real.pi := le_of_lt v21_pi_lower
  have hpiU : Real.pi ≤ v21RootPiU := le_of_lt v21_pi_upper
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hLN : 0 ≤ L - (N : ℝ) := sub_nonneg.mpr hNL
  have hUN : 0 ≤ U - (N : ℝ) := by linarith
  have hlo :
      v21RootPiL * (L - (N : ℝ)) ≤ v26LocalPhase N x := by
    unfold v26LocalPhase
    calc
      v21RootPiL * (L - (N : ℝ))
          ≤ Real.pi * (L - (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hpiL hLN
      _ ≤ Real.pi * (x - (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hhi :
      v26LocalPhase N x ≤ v21RootPiU * (U - (N : ℝ)) := by
    unfold v26LocalPhase
    calc
      Real.pi * (x - (N : ℝ))
          ≤ Real.pi * (U - (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      _ ≤ v21RootPiU * (U - (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hpiU hUN
  exact v26_sin_ball_between
    (mul_nonneg hpiL0 hLN) hlo hhi hphase

lemma v26_cos_local_right_ball {N : ℕ} {L U x : ℝ}
    (hNL : (N : ℝ) ≤ L) (hL : L ≤ x) (hU : x ≤ U)
    (hphase : v21RootPiU * (U - (N : ℝ)) ≤ 1) :
    v26Ball (Real.cos (v26LocalPhase N x))
      ((v21RootCosLower10 (v21RootPiU * (U - (N : ℝ))) +
          v21RootCosUpper8 (v21RootPiL * (L - (N : ℝ)))) / 2)
      ((v21RootCosUpper8 (v21RootPiL * (L - (N : ℝ))) -
          v21RootCosLower10 (v21RootPiU * (U - (N : ℝ)))) / 2) := by
  have hpiL : v21RootPiL ≤ Real.pi := le_of_lt v21_pi_lower
  have hpiU : Real.pi ≤ v21RootPiU := le_of_lt v21_pi_upper
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hLN : 0 ≤ L - (N : ℝ) := sub_nonneg.mpr hNL
  have hUN : 0 ≤ U - (N : ℝ) := by linarith
  have hlo :
      v21RootPiL * (L - (N : ℝ)) ≤ v26LocalPhase N x := by
    unfold v26LocalPhase
    calc
      v21RootPiL * (L - (N : ℝ))
          ≤ Real.pi * (L - (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hpiL hLN
      _ ≤ Real.pi * (x - (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hhi :
      v26LocalPhase N x ≤ v21RootPiU * (U - (N : ℝ)) := by
    unfold v26LocalPhase
    calc
      Real.pi * (x - (N : ℝ))
          ≤ Real.pi * (U - (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      _ ≤ v21RootPiU * (U - (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hpiU hUN
  exact v26_cos_ball_between
    (mul_nonneg hpiL0 hLN) hlo hhi hphase

/-- Sine enclosure on a final subcell lying to the left of its integer phase
    centre.  We enclose the positive distance phase and use oddness. -/
lemma v26_sin_local_left_ball {N : ℕ} {L U x : ℝ}
    (hUN : U ≤ (N : ℝ)) (hL : L ≤ x) (hU : x ≤ U)
    (hphase : v21RootPiU * ((N : ℝ) - L) ≤ 1) :
    v26Ball (Real.sin (v26LocalPhase N x))
      (-((v21RootSinLower7 (v21RootPiL * ((N : ℝ) - U)) +
          v21RootSinUpper9 (v21RootPiU * ((N : ℝ) - L))) / 2))
      ((v21RootSinUpper9 (v21RootPiU * ((N : ℝ) - L)) -
          v21RootSinLower7 (v21RootPiL * ((N : ℝ) - U))) / 2) := by
  have hpiL : v21RootPiL ≤ Real.pi := le_of_lt v21_pi_lower
  have hpiU : Real.pi ≤ v21RootPiU := le_of_lt v21_pi_upper
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hNU : 0 ≤ (N : ℝ) - U := sub_nonneg.mpr hUN
  have hNL : 0 ≤ (N : ℝ) - L := by linarith
  let t : ℝ := Real.pi * ((N : ℝ) - x)
  have hlo : v21RootPiL * ((N : ℝ) - U) ≤ t := by
    dsimp [t]
    calc
      v21RootPiL * ((N : ℝ) - U)
          ≤ Real.pi * ((N : ℝ) - U) :=
        mul_le_mul_of_nonneg_right hpiL hNU
      _ ≤ Real.pi * ((N : ℝ) - x) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hhi : t ≤ v21RootPiU * ((N : ℝ) - L) := by
    dsimp [t]
    calc
      Real.pi * ((N : ℝ) - x)
          ≤ Real.pi * ((N : ℝ) - L) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      _ ≤ v21RootPiU * ((N : ℝ) - L) :=
        mul_le_mul_of_nonneg_right hpiU hNL
  have hpos := v26_sin_ball_between
    (mul_nonneg hpiL0 hNU) hlo hhi hphase
  have hneg := v26_ball_neg hpos
  have hlocal : v26LocalPhase N x = -t := by
    dsimp [t]
    unfold v26LocalPhase
    ring
  rw [hlocal, Real.sin_neg]
  exact hneg

lemma v26_cos_local_left_ball {N : ℕ} {L U x : ℝ}
    (hUN : U ≤ (N : ℝ)) (hL : L ≤ x) (hU : x ≤ U)
    (hphase : v21RootPiU * ((N : ℝ) - L) ≤ 1) :
    v26Ball (Real.cos (v26LocalPhase N x))
      ((v21RootCosLower10 (v21RootPiU * ((N : ℝ) - L)) +
          v21RootCosUpper8 (v21RootPiL * ((N : ℝ) - U))) / 2)
      ((v21RootCosUpper8 (v21RootPiL * ((N : ℝ) - U)) -
          v21RootCosLower10 (v21RootPiU * ((N : ℝ) - L))) / 2) := by
  have hpiL : v21RootPiL ≤ Real.pi := le_of_lt v21_pi_lower
  have hpiU : Real.pi ≤ v21RootPiU := le_of_lt v21_pi_upper
  have hpiL0 : 0 ≤ v21RootPiL := by norm_num [v21RootPiL]
  have hNU : 0 ≤ (N : ℝ) - U := sub_nonneg.mpr hUN
  have hNL : 0 ≤ (N : ℝ) - L := by linarith
  let t : ℝ := Real.pi * ((N : ℝ) - x)
  have hlo : v21RootPiL * ((N : ℝ) - U) ≤ t := by
    dsimp [t]
    calc
      v21RootPiL * ((N : ℝ) - U)
          ≤ Real.pi * ((N : ℝ) - U) :=
        mul_le_mul_of_nonneg_right hpiL hNU
      _ ≤ Real.pi * ((N : ℝ) - x) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hhi : t ≤ v21RootPiU * ((N : ℝ) - L) := by
    dsimp [t]
    calc
      Real.pi * ((N : ℝ) - x)
          ≤ Real.pi * ((N : ℝ) - L) :=
        mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      _ ≤ v21RootPiU * ((N : ℝ) - L) :=
        mul_le_mul_of_nonneg_right hpiU hNL
  have hpos := v26_cos_ball_between
    (mul_nonneg hpiL0 hNU) hlo hhi hphase
  have hlocal : v26LocalPhase N x = -t := by
    dsimp [t]
    unfold v26LocalPhase
    ring
  rw [hlocal, Real.cos_neg]
  exact hpos

end HurtadoZeta23
