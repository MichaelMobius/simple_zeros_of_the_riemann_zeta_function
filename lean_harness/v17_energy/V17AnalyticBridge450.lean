import HurtadoZeta23.V17CompactOverlapCore
import HurtadoZeta23.V17KernelBridge450
import HurtadoZeta23.V17MatrixEnergy450
import Mathlib.Tactic

noncomputable section

open Matrix Finset Real Filter Topology
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Analytic kernel-to-Gram bridge for v17 length 450

The compact-overlap estimate is pointwise in two ordinates and is not tied to
the historical block length 262.  This file exposes that block-length-free
statement for the ordered retained columns and then restricts it to an
arbitrary consecutive principal block of length 450.

All finite-T shifted-pinching and external-certificate closures have been
removed from this dependency chain.
-/

/-- Any ordered retained zero enjoys the literal discrete centrality required
by the p=4 tail estimate. -/
theorem v17_orderedRetainedZero_criticalGridCentrality
    {T : ℝ}
    (hl : 0 < Zeta23.l T)
    (i : Fin (articleRetainedCard T))
    {M : ℕ}
    (hM : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2) :
    CriticalGridCentrality
      T (articleCriticalStep T) 0 (articleLastGridIndex T) M
      (orderedRetainedZero T i).im := by
  have hstep : 0 < articleCriticalStep T := articleCriticalStep_pos hl
  have hband := orderedRetainedZero_im_central T i
  have hmargin0 :
      articleCriticalStep T * ((M : ℝ) + 2) ≤
        articleCriticalStep T * (Zeta23.l T) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hM (le_of_lt hstep)
  have hmargin :
      articleCriticalStep T * ((M : ℝ) + 2) ≤ interiorBoundaryWidth T := by
    calc
      articleCriticalStep T * ((M : ℝ) + 2)
          ≤ articleCriticalStep T * (Zeta23.l T) ^ 2 := hmargin0
      _ = interiorBoundaryWidth T := articleCriticalStep_mul_l_sq hl
  exact criticalGridCentrality_of_continuous_band
    hstep hband.1 hband.2 (articleLastGridPoint_lower hl) hmargin

/-- Exact fixed-height identity for two arbitrary ordered retained columns,
with the reversed orientation used by the limiting variable `y_j-y_i`. -/
theorem v17_orderedRetainedGram_re_eq_normalizedIntervalOverlap_rev
    {T : ℝ}
    (hc : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (i j : Fin (articleRetainedCard T)) :
    (articleGlobalSimpleGram T
        (orderedRetainedColumn T i)
        (orderedRetainedColumn T j)).re =
      normalizedIntervalOverlap
        articleParams.ϱ (articleParams.L T) articleParams.w T
        (orderedRetainedZero T j).im (orderedRetainedZero T i).im
        0 (articleLastGridIndex T) := by
  have hbase :
      (articleGlobalSimpleGram T
          (orderedRetainedColumn T i)
          (orderedRetainedColumn T j)).re =
        normalizedIntervalOverlap
          articleParams.ϱ (articleParams.L T) articleParams.w T
          (orderedRetainedZero T i).im (orderedRetainedZero T j).im
          0 (articleLastGridIndex T) := by
    rw [articleGlobalSimpleGram_re_eq_finiteOverlap hc]
    rw [articleFiniteOverlapFin_eq_intervalFiniteGridOverlap]
    unfold normalizedIntervalOverlap
    rw [article_atD_a_eq_phiDMean T]
    simp only [Zeta23.Params.atD_L]
    rfl
  rw [hbase]
  exact normalizedIntervalOverlap_swap
    T (orderedRetainedZero T i).im (orderedRetainedZero T j).im

/-- The normalized ordinate difference is exactly the scaled ordinary-ordinate
difference, for arbitrary ordered retained ranks. -/
theorem v17_orderedRetainedY_sub_eq_scaled_im_sub
    (T : ℝ)
    (i j : Fin (articleRetainedCard T)) :
    orderedRetainedY T j - orderedRetainedY T i =
      articleParams.L T *
        ((orderedRetainedZero T j).im - (orderedRetainedZero T i).im) /
          (2 * Real.pi) := by
  unfold orderedRetainedY
  ring

/-- Quantitative compact-overlap estimate for two arbitrary ordered retained
columns.  This is the block-length-free analytic statement needed by v17. -/
theorem v17_orderedRetainedGram_compact_quantitative
    {T : ℝ}
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall : 4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (i j : Fin (articleRetainedCard T)) :
    |(articleGlobalSimpleGram T
        (orderedRetainedColumn T i)
        (orderedRetainedColumn T j)).re -
      limitingk (orderedRetainedY T j - orderedRetainedY T i)|
      ≤ v17ArticleCompactError T M := by
  have hcentj := v17_orderedRetainedZero_criticalGridCentrality hl j hM2
  have hcenti := v17_orderedRetainedZero_criticalGridCentrality hl i hM2

  have htail :
      |intervalFiniteGridOverlap
          articleParams.ϱ 1 (articleParams.L T) articleParams.w T
          (orderedRetainedZero T j).im (orderedRetainedZero T i).im
          0 (articleLastGridIndex T) -
        fullGridOverlap
          articleParams.ϱ 1 (articleParams.L T) articleParams.w
          (orderedRetainedZero T j).im (orderedRetainedZero T i).im|
        ≤ v17ArticleRawTailBound T M := by
    have h :=
      intervalFiniteGridOverlap_error_le_p4
        (ϱ := articleParams.ϱ)
        (lam := 1)
        (L := articleParams.L T)
        (w := articleParams.w)
        (T := T)
        (τ := (orderedRetainedZero T j).im)
        (τ' := (orderedRetainedZero T i).im)
        (kMin := 0)
        (kMax := articleLastGridIndex T)
        (M := M)
        articleParams_valid.taper
        one_pos
        le_rfl
        articleParams_valid.one_le_w
        hwL
        hkk
        hM1
        (by simpa [articleCriticalStep] using hcentj.1)
        (by simpa [articleCriticalStep] using hcenti.2)
    simpa [v17ArticleRawTailBound, articleCriticalStep] using h

  have hquant :=
    compactOverlap_quantitative
      (ϱ := articleParams.ϱ)
      (L := articleParams.L T)
      (w := articleParams.w)
      (T := T)
      (τ := (orderedRetainedZero T j).im)
      (τ' := (orderedRetainedZero T i).im)
      (tailErr := v17ArticleRawTailBound T M)
      (kMin := 0)
      (kMax := articleLastGridIndex T)
      articleParams_valid.taper
      articleParams_valid.one_le_w
      hwL
      hsmall
      htail

  rw [v17_orderedRetainedGram_re_eq_normalizedIntervalOverlap_rev hnorm i j]
  rw [v17_orderedRetainedY_sub_eq_scaled_im_sub T i j]
  simpa [v17ArticleCompactError] using hquant

/-- Rank `s+i` inside an arbitrary full consecutive retained block of length
450. -/
noncomputable def v17RetainedRank450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (i : Fin 450) : Fin (articleRetainedCard T) :=
  ⟨s + i.1, by
    have hi : i.1 < 450 := i.2
    omega⟩

/-- Global simple column selected by local coordinate `i : Fin 450`. -/
noncomputable def v17SimpleColumn450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (i : Fin 450) : ArticleSimpleColumn T :=
  orderedRetainedColumn T (v17RetainedRank450 T s hs i)

/-- Actual 450-by-450 principal Gram block. -/
noncomputable def v17Gram450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    Matrix (Fin 450) (Fin 450) ℂ :=
  principalGramBlock (articleGlobalSimpleGram T) (v17SimpleColumn450 T s hs)

/-- Totalized normalized ordinate sequence for the 450 block. -/
noncomputable def v17Y450
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (a : ℕ) : ℝ :=
  if ha : a < 450 then
    orderedRetainedY T (v17RetainedRank450 T s hs ⟨a, ha⟩)
  else 0

lemma v17Y450_of_lt
    (T : ℝ) (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    {a : ℕ} (ha : a < 450) :
    v17Y450 T s hs a =
      orderedRetainedY T (v17RetainedRank450 T s hs ⟨a, ha⟩) := by
  simp [v17Y450, ha]

/-- The generic compact-overlap theorem specialized to an actual v17
450-point principal block. -/
theorem v17_Gram450_compact_quantitative
    {T : ℝ}
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall : 4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (i j : Fin 450) :
    |(v17Gram450 T s hs i j).re -
      limitingk (v17Y450 T s hs j.1 - v17Y450 T s hs i.1)|
      ≤ v17ArticleCompactError T M := by
  change
    |(articleGlobalSimpleGram T
        (v17SimpleColumn450 T s hs i)
        (v17SimpleColumn450 T s hs j)).re -
      limitingk (v17Y450 T s hs j.1 - v17Y450 T s hs i.1)|
      ≤ v17ArticleCompactError T M
  rw [v17Y450_of_lt T s hs j.2, v17Y450_of_lt T s hs i.2]
  unfold v17SimpleColumn450
  exact v17_orderedRetainedGram_compact_quantitative
    hnorm hl hwL hsmall hM1 hM2 hkk
    (v17RetainedRank450 T s hs i)
    (v17RetainedRank450 T s hs j)

/-- Pointwise squared kernel lower bound for every pair inside the actual
450-point Gram block. -/
theorem v17_Gram450_pointwise_squared_lower
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall : 4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T)
    (a b : ℕ)
    (ha : a < 450)
    (hb : b < 450) :
    limitingWeightOnPoints (v17Y450 T s hs) a b -
        2 * v17ArticleCompactError T M
      ≤ ‖v17Gram450 T s hs ⟨a, ha⟩ ⟨b, hb⟩‖ ^ 2 := by
  let ia : Fin 450 := ⟨a, ha⟩
  let ib : Fin 450 := ⟨b, hb⟩
  let z : ℂ := v17Gram450 T s hs ia ib
  let kval : ℝ := limitingk (v17Y450 T s hs b - v17Y450 T s hs a)
  let eps : ℝ := v17ArticleCompactError T M

  have heps : 0 ≤ eps := by
    exact v17ArticleCompactError_nonneg hl M

  have hraw : |z.re - kval| ≤ eps := by
    dsimp [z, kval, eps, ia, ib]
    exact v17_Gram450_compact_quantitative
      hnorm hl hwL hsmall hM1 hM2 hkk s hs ⟨a, ha⟩ ⟨b, hb⟩

  have hgram : |z.re| ≤ 1 := by
    change
      |(articleGlobalSimpleGram T
          (v17SimpleColumn450 T s hs ia)
          (v17SimpleColumn450 T s hs ib)).re| ≤ 1
    exact v17_articleGlobalSimpleGram_re_abs_le_one
      T hPois hnorm
      (v17SimpleColumn450 T s hs ia)
      (v17SimpleColumn450 T s hs ib)

  have hk : |kval| ≤ 1 := by
    dsimp [kval]
    exact v17_limitingk_abs_le_one _

  have hsquare : kval ^ 2 - 2 * eps ≤ z.re ^ 2 :=
    sq_lower_of_abs_sub_le heps hgram hk hraw

  have hreNorm : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hprod : 0 ≤ (‖z‖ - |z.re|) * (‖z‖ + |z.re|) := by
    exact mul_nonneg
      (sub_nonneg.mpr hreNorm)
      (add_nonneg (norm_nonneg z) (abs_nonneg z.re))
  have habsSq : |z.re| ^ 2 = z.re ^ 2 := by simp
  have hreSq : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [hprod, habsSq]

  change
    limitingk (v17Y450 T s hs b - v17Y450 T s hs a) ^ 2 -
        2 * v17ArticleCompactError T M
      ≤ ‖v17Gram450 T s hs ⟨a, ha⟩ ⟨b, hb⟩‖ ^ 2
  dsimp [kval, eps, z, ia, ib] at hsquare hreSq
  exact hsquare.trans hreSq

/-- Aggregated directed pair-energy consequence for the actual 450-point
block.  The analytic loss is the exact finite count `404100 * eps`. -/
theorem v17_Gram450_global_pair_energy_lower
    {T : ℝ}
    (hPois : Zeta23.ZeroSide.PoissonSq T (articleParams.atD T))
    (hnorm : 0 < (articleParams.atD T).a T * (articleParams.atD T).L T ^ 2)
    (hl : 0 < Zeta23.l T)
    (hwL : 8 * articleParams.w ≤ articleParams.L T)
    (hsmall : 4 * articleParams.w / articleParams.L T ≤ limitingK 0 / 2)
    {M : ℕ}
    (hM1 : 1 ≤ M)
    (hM2 : (M : ℝ) + 2 ≤ (Zeta23.l T) ^ 2)
    (hkk : (0 : ℤ) ≤ articleLastGridIndex T)
    (s : ℕ)
    (hs : s + 450 ≤ articleRetainedCard T) :
    globalPairEnergyNat 450 (limitingWeightOnPoints (v17Y450 T s hs)) -
        404100 * v17ArticleCompactError T M
      ≤ globalPairEnergyNat 450
          (v17MatrixNormSqNat450 (v17Gram450 T s hs)) := by
  apply v17_aggregate_kernel_lower_450_of_pointwise_raw_loss
  intro a b ha hb
  simpa [v17MatrixNormSqNat450, ha, hb] using
    v17_Gram450_pointwise_squared_lower
      hPois hnorm hl hwL hsmall hM1 hM2 hkk s hs a b ha hb

end HurtadoZeta23
