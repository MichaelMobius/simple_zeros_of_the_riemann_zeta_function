import HurtadoZeta23.V26E3GlobalClosure
import HurtadoZeta23.ArticleBlockErrorSmall
import Zeta23.Statement.SeamClosed
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

noncomputable section

open Filter Asymptotics Topology

namespace HurtadoZeta23

/-- The dyadic proportion of simple critical-line zeros.  The denominator is
nonzero eventually by `eventually_one_le_globalN`; values at small heights are
irrelevant to the `atTop` liminf. -/
def v26SimpleRatio (T : ℝ) : ℝ :=
  (Zeta23.N0simple T (2 * T) : ℝ) /
    (Zeta23.Ncount T (2 * T) : ℝ)

/-- The published epsilon-form implies the corresponding eventual lower bound
for the normalized ratio. -/
theorem v26_eventually_publishedConstant_sub_eps_le_ratio
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      v17PublishedConstant - ε ≤ v26SimpleRatio T := by
  rcases v26_published_eps_form ε hε with ⟨T₀, hT₀⟩
  filter_upwards [eventually_ge_atTop T₀, eventually_one_le_globalN]
    with T hT hN1
  have hmain := hT₀ T hT
  change (1 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) at hN1
  have hNpos : 0 < (Zeta23.Ncount T (2 * T) : ℝ) :=
    lt_of_lt_of_le zero_lt_one hN1
  unfold v26SimpleRatio
  exact (le_div_iff₀ hNpos).2 hmain

/-- The same ratio is eventually at most one, using the hypothesis-free
trivial counting chain `N₀ˢ ≤ N`. -/
theorem v26_eventually_simpleRatio_le_one :
    ∀ᶠ T : ℝ in atTop, v26SimpleRatio T ≤ 1 := by
  filter_upwards [eventually_one_le_globalN] with T hN1
  change (1 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) at hN1
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
  unfold v26SimpleRatio
  apply (div_le_iff₀ hNpos).2
  simpa using hReal

/-- Literal liminf form of the v26 published theorem. -/
theorem v26_published_liminf :
    v17PublishedConstant ≤
      Filter.liminf v26SimpleRatio Filter.atTop := by
  have hupper :
      Filter.atTop.IsBoundedUnder (· ≤ ·) v26SimpleRatio :=
    Filter.isBoundedUnder_of_eventually_le v26_eventually_simpleRatio_le_one
  have hcob :
      Filter.atTop.IsCoboundedUnder (· ≥ ·) v26SimpleRatio :=
    hupper.isCoboundedUnder_ge
  have hεinf :
      ∀ ε : ℝ, 0 < ε →
        v17PublishedConstant - ε ≤
          Filter.liminf v26SimpleRatio Filter.atTop := by
    intro ε hε
    exact Filter.le_liminf_of_le hcob
      (v26_eventually_publishedConstant_sub_eps_le_ratio ε hε)
  by_contra hnot
  have hlt :
      Filter.liminf v26SimpleRatio Filter.atTop < v17PublishedConstant :=
    lt_of_not_ge hnot
  let ε : ℝ :=
    (v17PublishedConstant -
      Filter.liminf v26SimpleRatio Filter.atTop) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hbound := hεinf ε hεpos
  dsimp [ε] at hbound
  linarith

end HurtadoZeta23
