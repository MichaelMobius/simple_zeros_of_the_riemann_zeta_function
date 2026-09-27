import Zeta23.Statement.SeamClosed
import Zeta23.Assembly
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-!
# Research-only generic epsilon-to-liminf endpoint

This module deliberately contains no window, certificate, or block argument.
It proves once and for all that an eventual dyadic epsilon-form lower bound
implies the literal `liminf` statement for the simple-zero proportion.
-/

/-- The dyadic total zero count tends to infinity. -/
theorem research9_eventually_one_le_globalN :
    ∀ᶠ T : ℝ in atTop,
      (1 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by
  have hNtop :
      Tendsto (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ))
        atTop atTop := by
    simpa only [Zeta23.zetaZeroConfig_N] using
      (Zeta23.Assembly.tendsto_N_atTop
        Zeta23.zetaZeroConfig
        (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts))
  exact hNtop.eventually_ge_atTop (1 : ℝ)

/-- Dyadic proportion of simple critical-line zeros. -/
def research9SimpleRatio (T : ℝ) : ℝ :=
  (Zeta23.N0simple T (2 * T) : ℝ) /
    (Zeta23.Ncount T (2 * T) : ℝ)

/-- The simple-zero ratio is eventually at most one. -/
theorem research9_eventually_simpleRatio_le_one :
    ∀ᶠ T : ℝ in atTop, research9SimpleRatio T ≤ 1 := by
  filter_upwards [research9_eventually_one_le_globalN] with T hN1
  have hNpos : 0 < (Zeta23.Ncount T (2 * T) : ℝ) :=
    lt_of_lt_of_le zero_lt_one hN1
  have hchain := Zeta23.trivial_chain₀ T (2 * T)
  have hNat :
      Zeta23.N0simple T (2 * T) ≤ Zeta23.Ncount T (2 * T) :=
    hchain.1.trans (hchain.2.1.trans hchain.2.2.1)
  have hReal :
      (Zeta23.N0simple T (2 * T) : ℝ) ≤
        (Zeta23.Ncount T (2 * T) : ℝ) := by
    exact_mod_cast hNat
  unfold research9SimpleRatio
  apply (div_le_iff₀ hNpos).2
  simpa using hReal

/-- An epsilon-form lower bound at a constant `C` gives the corresponding
eventual lower bound for the normalized ratio. -/
theorem research9_eventually_sub_eps_le_ratio_of_eps_form
    {C : ℝ}
    (hform : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (C - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, C - ε ≤ research9SimpleRatio T := by
  rcases hform ε hε with ⟨T₀, hT₀⟩
  filter_upwards [eventually_ge_atTop T₀, research9_eventually_one_le_globalN]
    with T hT hN1
  have hmain := hT₀ T hT
  have hNpos : 0 < (Zeta23.Ncount T (2 * T) : ℝ) :=
    lt_of_lt_of_le zero_lt_one hN1
  unfold research9SimpleRatio
  exact (le_div_iff₀ hNpos).2 hmain

/-- Generic literal liminf endpoint.  This is the final asymptotic bridge used
by the research candidate once its global epsilon-form has been established. -/
theorem research9_liminf_of_eps_form
    {C : ℝ}
    (hform : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (C - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T)) :
    C ≤ Filter.liminf research9SimpleRatio Filter.atTop := by
  have hupper :
      Filter.atTop.IsBoundedUnder (· ≤ ·) research9SimpleRatio :=
    Filter.isBoundedUnder_of_eventually_le research9_eventually_simpleRatio_le_one
  have hcob :
      Filter.atTop.IsCoboundedUnder (· ≥ ·) research9SimpleRatio :=
    hupper.isCoboundedUnder_ge
  have hεinf :
      ∀ ε : ℝ, 0 < ε →
        C - ε ≤ Filter.liminf research9SimpleRatio Filter.atTop := by
    intro ε hε
    exact Filter.le_liminf_of_le hcob
      (research9_eventually_sub_eps_le_ratio_of_eps_form hform ε hε)
  by_contra hnot
  have hlt : Filter.liminf research9SimpleRatio Filter.atTop < C :=
    lt_of_not_ge hnot
  let ε : ℝ := (C - Filter.liminf research9SimpleRatio Filter.atTop) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hbound := hεinf ε hεpos
  dsimp [ε] at hbound
  linarith

end HurtadoZeta23
