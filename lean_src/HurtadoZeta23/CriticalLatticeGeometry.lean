import HurtadoZeta23.TwoSidedGridTail
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

open Real Filter Topology
open scoped BigOperators

/-- A point of the critical lattice `T + k * step`, with integer index `k`. -/
def criticalGridPoint (T step : ℝ) (k : ℤ) : ℝ :=
  T + (k : ℝ) * step

/-- The omitted integer index on the left, reindexed so that the analytic tail
parameter itself starts at the endpoint margin `M`.  For `n ≥ M` this is
`kMin - 1 - (n-M)`. -/
def leftOmittedIndex (kMin : ℤ) (M n : ℕ) : ℤ :=
  kMin - 1 - Int.ofNat (n - M)

/-- The corresponding omitted integer index on the right. -/
def rightOmittedIndex (kMax : ℤ) (M n : ℕ) : ℤ :=
  kMax + 1 + Int.ofNat (n - M)

/-- A retained frequency is `M` cells inside both endpoints of the finite
critical lattice.  This is the literal geometric hypothesis used in Appendix IV. -/
def CriticalGridCentrality
    (T step : ℝ) (kMin kMax : ℤ) (M : ℕ) (τ : ℝ) : Prop :=
  0 < step ∧
  criticalGridPoint T step kMin + step * (M : ℝ) ≤ τ ∧
  τ ≤ criticalGridPoint T step kMax - step * (M : ℝ)

lemma leftOmittedIndex_gridPoint
    {T step : ℝ} {kMin : ℤ} {M n : ℕ} (hn : M ≤ n) :
    criticalGridPoint T step (leftOmittedIndex kMin M n) =
      criticalGridPoint T step kMin - step * (1 + ((n - M : ℕ) : ℝ)) := by
  unfold criticalGridPoint leftOmittedIndex
  have hInt :
      ((Int.ofNat (n - M) : ℤ) : ℝ) =
        ((n - M : ℕ) : ℝ) := by
    exact Int.cast_natCast (n - M)
  have hNat :
      ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
    exact Nat.cast_sub hn
  rw [Int.cast_sub, Int.cast_sub, Int.cast_one, hInt, hNat]
  ring

lemma rightOmittedIndex_gridPoint
    {T step : ℝ} {kMax : ℤ} {M n : ℕ} (hn : M ≤ n) :
    criticalGridPoint T step (rightOmittedIndex kMax M n) =
      criticalGridPoint T step kMax + step * (1 + ((n - M : ℕ) : ℝ)) := by
  unfold criticalGridPoint rightOmittedIndex
  have hInt :
      ((Int.ofNat (n - M) : ℤ) : ℝ) =
        ((n - M : ℕ) : ℝ) := by
    exact Int.cast_natCast (n - M)
  have hNat :
      ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
    exact Nat.cast_sub hn
  rw [Int.cast_add, Int.cast_add, Int.cast_one, hInt, hNat]
  ring

/-- Centrality gives the exact lower-distance estimate for every omitted
left-lattice point. -/
theorem left_omitted_distance
    {T step τ : ℝ} {kMin kMax : ℤ} {M n : ℕ}
    (hc : CriticalGridCentrality T step kMin kMax M τ)
    (hn : M ≤ n) :
    step * (n : ℝ) ≤
      |τ - criticalGridPoint T step (leftOmittedIndex kMin M n)| := by
  rcases hc with ⟨hstep, hleft, _⟩
  rw [leftOmittedIndex_gridPoint hn]
  have hnonneg :
      0 ≤ τ - (criticalGridPoint T step kMin -
        step * (1 + ((n - M : ℕ) : ℝ))) := by
    have hcast : ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
      rw [Nat.cast_sub hn]
    rw [hcast]
    nlinarith
  rw [abs_of_nonneg hnonneg]
  have hcast : ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
    rw [Nat.cast_sub hn]
  rw [hcast]
  nlinarith

/-- Centrality gives the symmetric lower-distance estimate for every omitted
right-lattice point. -/
theorem right_omitted_distance
    {T step τ : ℝ} {kMin kMax : ℤ} {M n : ℕ}
    (hc : CriticalGridCentrality T step kMin kMax M τ)
    (hn : M ≤ n) :
    step * (n : ℝ) ≤
      |τ - criticalGridPoint T step (rightOmittedIndex kMax M n)| := by
  rcases hc with ⟨hstep, _, hright⟩
  rw [rightOmittedIndex_gridPoint hn]
  have hnonpos :
      τ - (criticalGridPoint T step kMax +
        step * (1 + ((n - M : ℕ) : ℝ))) ≤ 0 := by
    have hcast : ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
      rw [Nat.cast_sub hn]
    rw [hcast]
    nlinarith
  rw [abs_of_nonpos hnonpos]
  have hcast : ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
    rw [Nat.cast_sub hn]
  rw [hcast]
  nlinarith

/-- The left omitted half-grid satisfies exactly the geometry interface used
by the p=4 Fourier tail argument, simultaneously for `τ` and `τ'`. -/
theorem left_halfGridDistanceGeometry
    {T step τ τ' : ℝ} {kMin kMax : ℤ} {M : ℕ}
    (hcτ : CriticalGridCentrality T step kMin kMax M τ)
    (hcτ' : CriticalGridCentrality T step kMin kMax M τ') :
    HalfGridDistanceGeometry step M
      (fun n => τ - criticalGridPoint T step (leftOmittedIndex kMin M n))
      (fun n => τ' - criticalGridPoint T step (leftOmittedIndex kMin M n)) := by
  refine ⟨hcτ.1, ?_⟩
  intro n hn
  exact ⟨left_omitted_distance hcτ hn, left_omitted_distance hcτ' hn⟩

/-- The analogous geometry statement for the right omitted half-grid. -/
theorem right_halfGridDistanceGeometry
    {T step τ τ' : ℝ} {kMin kMax : ℤ} {M : ℕ}
    (hcτ : CriticalGridCentrality T step kMin kMax M τ)
    (hcτ' : CriticalGridCentrality T step kMin kMax M τ') :
    HalfGridDistanceGeometry step M
      (fun n => τ - criticalGridPoint T step (rightOmittedIndex kMax M n))
      (fun n => τ' - criticalGridPoint T step (rightOmittedIndex kMax M n)) := by
  refine ⟨hcτ.1, ?_⟩
  intro n hn
  exact ⟨right_omitted_distance hcτ hn, right_omitted_distance hcτ' hn⟩

/-- Literal left omitted Gabor summand for `phiD`. -/
def leftOmittedPhiDSummand
    (ϱ : ℝ → ℝ) (lam L w T step τ τ' : ℝ)
    (kMin : ℤ) (M : ℕ) (n : ℕ) : ℝ :=
  Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD ϱ lam L w)
      (τ - criticalGridPoint T step (leftOmittedIndex kMin M n)) *
  Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD ϱ lam L w)
      (τ' - criticalGridPoint T step (leftOmittedIndex kMin M n))

/-- Literal right omitted Gabor summand for `phiD`. -/
def rightOmittedPhiDSummand
    (ϱ : ℝ → ℝ) (lam L w T step τ τ' : ℝ)
    (kMax : ℤ) (M : ℕ) (n : ℕ) : ℝ :=
  Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD ϱ lam L w)
      (τ - criticalGridPoint T step (rightOmittedIndex kMax M n)) *
  Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD ϱ lam L w)
      (τ' - criticalGridPoint T step (rightOmittedIndex kMax M n))

/-- The centrality hypothesis itself now supplies the left p=4 majorant. -/
theorem leftOmittedPhiD_majorized
    {ϱ : ℝ → ℝ} {lam L w T step τ τ' : ℝ}
    {kMin kMax : ℤ} {M : ℕ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hM : 1 ≤ M)
    (hcτ : CriticalGridCentrality T step kMin kMax M τ)
    (hcτ' : CriticalGridCentrality T step kMin kMax M τ') :
    UniformHalfTailMajorized
      (leftOmittedPhiDSummand ϱ lam L w T step τ τ' kMin M)
      (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2) step M := by
  exact phiD_half_tail_p4_majorant hϱ h0 h1 hw hwL hM
    (left_halfGridDistanceGeometry hcτ hcτ')

/-- The symmetric right p=4 majorant, again with no abstract geometry input. -/
theorem rightOmittedPhiD_majorized
    {ϱ : ℝ → ℝ} {lam L w T step τ τ' : ℝ}
    {kMin kMax : ℤ} {M : ℕ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hM : 1 ≤ M)
    (hcτ : CriticalGridCentrality T step kMin kMax M τ)
    (hcτ' : CriticalGridCentrality T step kMin kMax M τ') :
    UniformHalfTailMajorized
      (rightOmittedPhiDSummand ϱ lam L w T step τ τ' kMax M)
      (((Zeta23.ThmD.cDT ϱ lam) / w) ^ 2) step M := by
  exact phiD_half_tail_p4_majorant hϱ h0 h1 hw hwL hM
    (right_halfGridDistanceGeometry hcτ hcτ')

/-- Consequently, for fixed window/lattice parameters and any positive error,
the literal two-sided omitted critical lattice is uniformly small once the
endpoint margin is sufficiently large. -/
theorem eventually_literal_phiD_twoSidedTail_lt
    {ϱ : ℝ → ℝ} {lam L w T step : ℝ} {kMin kMax : ℤ} {eps : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ)
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hstep : 0 < step) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop,
      ∀ τ τ' : ℝ,
        CriticalGridCentrality T step kMin kMax M τ →
        CriticalGridCentrality T step kMin kMax M τ' →
        |twoSidedTail
          (leftOmittedPhiDSummand ϱ lam L w T step τ τ' kMin M)
          (rightOmittedPhiDSummand ϱ lam L w T step τ τ' kMax M)
          M| < eps := by
  have hC : 0 ≤ ((Zeta23.ThmD.cDT ϱ lam / w) ^ 2) := sq_nonneg _
  have htail := eventually_abs_twoSidedTail_lt_of_geometry hC hstep heps
  have hMpos : ∀ᶠ M : ℕ in atTop, 1 ≤ M := eventually_ge_atTop 1
  filter_upwards [htail, hMpos] with M htailM hM1
  intro τ τ' hcτ hcτ'
  exact htailM _ _
    (leftOmittedPhiD_majorized hϱ h0 h1 hw hwL hM1 hcτ hcτ')
    (rightOmittedPhiD_majorized hϱ h0 h1 hw hwL hM1 hcτ hcτ')

end HurtadoZeta23
