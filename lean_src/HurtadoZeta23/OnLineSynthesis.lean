import HurtadoZeta23.RootMultisetGramBridge
import HurtadoZeta23.StableRankTraceMatrix
import Zeta23.ZeroSide
import Mathlib.Tactic

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace HurtadoZeta23

/-- `matrixSpectralDefect` respects equality of the underlying PSD matrix.
This explicit wrapper avoids dependent `rw` motives involving PSD witnesses. -/
lemma matrixSpectralDefect_eq_of_matrix_eq
    {K : Type*} [RCLike K]
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n K}
    (hA : A.PosSemidef)
    (hB : B.PosSemidef)
    (r : ℕ)
    (hAB : A = B) :
    matrixSpectralDefect A hA r = matrixSpectralDefect B hB r := by
  subst B
  rfl

/-- `gramSpectralDefect` likewise respects equality of its PSD Gram matrix. -/
lemma gramSpectralDefect_eq_of_matrix_eq
    {K : Type*} [RCLike K]
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n K}
    (hA : A.PosSemidef)
    (hB : B.PosSemidef)
    (hAB : A = B) :
    gramSpectralDefect A hA = gramSpectralDefect B hB := by
  subst B
  rfl

/-!
# On-line synthesis matrices

There are two distinct factorizations in this file.

* `onLineSynthesis` factors Anthropic's full positive on-line block `hatP`.
  Its columns are all distinct on-line zeros, simple and multiple, so its
  column count is `s₁+s₂`.  This is a useful auxiliary identity.

* `simpleOnLineSynthesis` is the matrix used by the article.  Its columns are
  only the simple critical-line zeros `S₁`, so its column count is exactly
  `s₁`.  Its Gram matrix is the `M = VᴴV` whose defect appears in the paper.
-/

section AbstractBlock

variable {ι d : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Column index type for the complete on-line block. -/
abbrev OnLineColumn (D : Zeta23.ZeroSide.ZeroBlockData ι d) :=
  {z : ι // z ∈ D.onLine}

/-- Column index type for the simple critical-line block `S₁`. -/
abbrev SimpleOnLineColumn (D : Zeta23.ZeroSide.ZeroBlockData ι d) :=
  {z : ι // z ∈ D.S₁}

/-- A point of `S₁` is on the critical line. -/
lemma mem_onLine_of_mem_S₁
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {z : ι} (hz : z ∈ D.S₁) : z ∈ D.onLine := by
  rw [D.onLine_eq_S₁_union_S₂]
  exact Finset.mem_union_left _ hz

/-- A point of `S₂` is on the critical line. -/
lemma mem_onLine_of_mem_S₂
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {z : ι} (hz : z ∈ D.S₂) : z ∈ D.onLine := by
  rw [D.onLine_eq_S₁_union_S₂]
  exact Finset.mem_union_right _ hz

/-- Multiplicity is one on `S₁`. -/
lemma mult_eq_one_of_mem_S₁
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
  have h := hz
  simp only [Zeta23.ZeroSide.ZeroBlockData.S₁, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  exact h.2

/-- The normalized synthesis matrix for all distinct on-line zeros.
Multiplicity is carried by the square-root weight. -/
def onLineSynthesis (D : Zeta23.ZeroSide.ZeroBlockData ι d) (c : ℝ) :
    Matrix d (OnLineColumn D) ℂ :=
  fun k z =>
    ((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) * D.v z.1 k

/-- The synthesis matrix used in the article: one column for each simple
critical-line zero.  Since `m=1` on `S₁`, the weight is exactly `1/sqrt c`. -/
def simpleOnLineSynthesis (D : Zeta23.ZeroSide.ZeroBlockData ι d) (c : ℝ) :
    Matrix d (SimpleOnLineColumn D) ℂ :=
  fun k z =>
    ((Real.sqrt ((D.m z.1 : ℝ) / c) : ℝ) : ℂ) * D.v z.1 k

/-- The complete on-line column type has cardinality `s₁+s₂`. -/
theorem card_onLineColumn (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    Fintype.card (OnLineColumn D) = D.s₁ + D.s₂ := by
  simpa [OnLineColumn] using D.card_onLine

/-- The article's simple-zero column type has cardinality exactly `s₁`. -/
theorem card_simpleOnLineColumn (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    Fintype.card (SimpleOnLineColumn D) = D.s₁ := by
  change Fintype.card ↥D.S₁ = #D.S₁
  exact Fintype.card_coe D.S₁

/-- On-line evaluation vectors are fixed by complex conjugation. -/
lemma conj_v_of_onLine (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (z : OnLineColumn D) (k : d) :
    star (D.v z.1 k) = D.v z.1 k := by
  have hz := D.star_v_of_onLine ((D.mem_onLine).mp z.2)
  have hk := congrFun hz k
  simpa [Pi.star_apply, RCLike.star_def] using hk

/-- The same reality statement for a simple critical-line column. -/
lemma conj_v_of_simpleOnLine (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (z : SimpleOnLineColumn D) (k : d) :
    star (D.v z.1 k) = D.v z.1 k := by
  have hzOn : z.1 ∈ D.onLine := mem_onLine_of_mem_S₁ D z.2
  have hz := D.star_v_of_onLine ((D.mem_onLine).mp hzOn)
  have hk := congrFun hz k
  simpa [Pi.star_apply, RCLike.star_def] using hk

/-- The square-root multiplicity normalization has the expected square. -/
lemma sq_sqrt_mult_div {m : ℕ} {c : ℝ} (hc : 0 < c) :
    (Real.sqrt ((m : ℝ) / c)) ^ 2 = (m : ℝ) / c := by
  rw [Real.sq_sqrt]
  positivity

/-- **Exact factorization of the complete on-line block.** -/
theorem blockP_eq_onLineSynthesis_mul_conjTranspose
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) {c : ℝ} (hc : 0 < c) :
    D.blockP c =
      onLineSynthesis D c * (onLineSynthesis D c).conjTranspose := by
  classical
  ext k l
  rw [Zeta23.ZeroSide.ZeroBlockData.blockP]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Zeta23.ZeroSide.ZeroBlockData.onPart]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_subtype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hreal := conj_v_of_onLine D z l
  have hsqrt := sq_sqrt_mult_div (m := D.m z) hc
  have hcoefR :
      c⁻¹ * (D.m z : ℝ) =
        Real.sqrt ((D.m z : ℝ) / c) *
          Real.sqrt ((D.m z : ℝ) / c) := by
    calc
      c⁻¹ * (D.m z : ℝ) = (D.m z : ℝ) / c := by
        rw [div_eq_mul_inv, mul_comm]
      _ = (Real.sqrt ((D.m z : ℝ) / c)) ^ 2 := hsqrt.symm
      _ = _ := by rw [pow_two]
  have hcoefC :
      (((c⁻¹ : ℝ) : ℂ) * (D.m z : ℂ)) =
        (((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) *
          ((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ)) := by
    exact_mod_cast hcoefR
  simp only [onLineSynthesis]
  rw [star_mul']
  rw [hreal]
  simp only [Complex.star_def, Complex.conj_ofReal]
  calc
    (((c⁻¹ : ℝ) : ℂ) *
        ((D.m z : ℂ) * (D.v z k * D.v z l))) =
      ((((c⁻¹ : ℝ) : ℂ) * (D.m z : ℂ)) *
        (D.v z k * D.v z l)) := by ring
    _ =
      ((((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) *
          ((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ)) *
        (D.v z k * D.v z l)) := by rw [hcoefC]
    _ =
      (((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) * D.v z k) *
        (((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) * D.v z l) := by
      ring
  intro x
  rfl

/-- Raw simple-line positive part, before the `c⁻¹` normalization. -/
def simplePart (D : Zeta23.ZeroSide.ZeroBlockData ι d) : Matrix d d ℂ :=
  ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- Raw multiple-line positive part, before the `c⁻¹` normalization. -/
def multiplePart (D : Zeta23.ZeroSide.ZeroBlockData ι d) : Matrix d d ℂ :=
  ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The normalized simple critical-line block `P₁` of the article. -/
def simpleBlockP (D : Zeta23.ZeroSide.ZeroBlockData ι d) (c : ℝ) : Matrix d d ℂ :=
  (((c⁻¹ : ℝ) : ℂ)) • simplePart D

/-- The normalized multiple critical-line positive remainder. -/
def multipleBlockP (D : Zeta23.ZeroSide.ZeroBlockData ι d) (c : ℝ) : Matrix d d ℂ :=
  (((c⁻¹ : ℝ) : ℂ)) • multiplePart D

/-- The full on-line block splits into the simple and multiple critical-line
positive pieces. -/
theorem blockP_eq_simpleBlockP_add_multipleBlockP
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) (c : ℝ) :
    D.blockP c = simpleBlockP D c + multipleBlockP D c := by
  unfold Zeta23.ZeroSide.ZeroBlockData.blockP
  unfold Zeta23.ZeroSide.ZeroBlockData.onPart
  unfold simpleBlockP multipleBlockP simplePart multiplePart
  rw [D.onLine_eq_S₁_union_S₂]
  rw [Finset.sum_union D.disjoint_S₁_S₂]
  rw [smul_add]

/-- The raw simple part is PSD. -/
theorem simplePart_posSemidef
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    (simplePart D).PosSemidef := by
  unfold simplePart
  refine Matrix.posSemidef_sum _ fun z hz => ?_
  have h :=
    Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
      (D.star_v_of_onLine ((D.mem_onLine).mp (mem_onLine_of_mem_S₁ D hz)))
      (Nat.cast_nonneg (D.m z))
  simpa using h

/-- The raw multiple-on-line part is PSD. -/
theorem multiplePart_posSemidef
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    (multiplePart D).PosSemidef := by
  unfold multiplePart
  refine Matrix.posSemidef_sum _ fun z hz => ?_
  have h :=
    Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
      (D.star_v_of_onLine ((D.mem_onLine).mp (mem_onLine_of_mem_S₂ D hz)))
      (Nat.cast_nonneg (D.m z))
  simpa using h

/-- The normalized simple block is PSD. -/
theorem simpleBlockP_posSemidef
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c) :
    (simpleBlockP D c).PosSemidef := by
  unfold simpleBlockP
  exact (simplePart_posSemidef D).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

/-- The normalized multiple block is PSD. -/
theorem multipleBlockP_posSemidef
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c) :
    (multipleBlockP D c).PosSemidef := by
  unfold multipleBlockP
  exact (multiplePart_posSemidef D).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

/-- Rank of the simple positive block is at most `s₁`. -/
theorem rank_simpleBlockP_le
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c) :
    (simpleBlockP D c).rank ≤ D.s₁ := by
  unfold simpleBlockP
  rw [Zeta23.ZeroSide.rank_smul_of_ne_zero _ (by
    exact_mod_cast (inv_ne_zero hc.ne'))]
  unfold simplePart
  refine (Zeta23.ZeroSide.rank_sum_le _ _ (fun _ => 1)
    (fun z _ => Zeta23.ZeroSide.rank_smul_vecMulVec_le _ _ _)).trans ?_
  simp [Zeta23.ZeroSide.ZeroBlockData.s₁]

/-- Rank of the multiple positive block is at most `s₂`. -/
theorem rank_multipleBlockP_le
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c) :
    (multipleBlockP D c).rank ≤ D.s₂ := by
  unfold multipleBlockP
  rw [Zeta23.ZeroSide.rank_smul_of_ne_zero _ (by
    exact_mod_cast (inv_ne_zero hc.ne'))]
  unfold multiplePart
  refine (Zeta23.ZeroSide.rank_sum_le _ _ (fun _ => 1)
    (fun z _ => Zeta23.ZeroSide.rank_smul_vecMulVec_le _ _ _)).trans ?_
  simp [Zeta23.ZeroSide.ZeroBlockData.s₂]

/-- Trace of the raw simple part as the sum of squared column norms. -/
lemma rtrace_simplePart
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) :
    rtrace (simplePart D) =
      ∑ z ∈ D.S₁, (D.m z : ℝ) * ∑ k, ‖D.v z k‖ ^ 2 := by
  unfold simplePart rtrace
  rw [trace_sum, map_sum]
  refine sum_congr rfl fun z hz => ?_
  have h := congrFun
    (D.star_v_of_onLine ((D.mem_onLine).mp (mem_onLine_of_mem_S₁ D hz)))
  rw [trace_smul, trace_vecMulVec, smul_eq_mul, dotProduct]
  have hsq :
      ∑ k, D.v z k * D.v z k =
        ((∑ k, ‖D.v z k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun k _ => ?_
    have hk : (starRingEnd ℂ) (D.v z k) = D.v z k := by
      have hk' := h k
      rwa [Pi.star_apply, RCLike.star_def] at hk'
    calc
      D.v z k * D.v z k = (starRingEnd ℂ) (D.v z k) * D.v z k := by rw [hk]
      _ = _ := RCLike.conj_mul (D.v z k)
  rw [hsq, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    RCLike.re_to_complex, Complex.ofReal_re]

/-- The article's column-norm bound implies `tr P₁ ≤ s₁`. -/
theorem rtrace_simpleBlockP_le
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.S₁, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (simpleBlockP D c) ≤ (D.s₁ : ℝ) := by
  have htr :
      rtrace (simpleBlockP D c) = c⁻¹ * rtrace (simplePart D) := by
    simp only [rtrace, simpleBlockP, trace_smul, smul_eq_mul,
      RCLike.re_to_complex, Complex.re_ofReal_mul]
  rw [htr, rtrace_simplePart, mul_sum]
  calc
    (∑ z ∈ D.S₁,
        c⁻¹ * ((D.m z : ℝ) * ∑ k, ‖D.v z k‖ ^ 2))
        ≤ ∑ z ∈ D.S₁, (1 : ℝ) := by
          refine sum_le_sum fun z hz => ?_
          have hm : D.m z = 1 := mult_eq_one_of_mem_S₁ D hz
          rw [hm]
          norm_num
          calc
            c⁻¹ * (∑ k, ‖D.v z k‖ ^ 2)
                ≤ c⁻¹ * c :=
                  mul_le_mul_of_nonneg_left (hPois z hz)
                    (inv_nonneg.mpr hc.le)
            _ = 1 := inv_mul_cancel₀ hc.ne'
    _ = (D.s₁ : ℝ) := by
      simp [Zeta23.ZeroSide.ZeroBlockData.s₁]

/-- Exact factorization of the simple critical-line block `P₁`. -/
theorem simpleBlockP_eq_simpleOnLineSynthesis_mul_conjTranspose
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ} (hc : 0 < c) :
    simpleBlockP D c =
      simpleOnLineSynthesis D c *
        (simpleOnLineSynthesis D c).conjTranspose := by
  classical
  ext k l
  rw [simpleBlockP]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [simplePart]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_subtype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hreal := conj_v_of_simpleOnLine D z l
  have hsqrt := sq_sqrt_mult_div (m := D.m z) hc
  have hcoefR :
      c⁻¹ * (D.m z : ℝ) =
        Real.sqrt ((D.m z : ℝ) / c) *
          Real.sqrt ((D.m z : ℝ) / c) := by
    calc
      c⁻¹ * (D.m z : ℝ) = (D.m z : ℝ) / c := by
        rw [div_eq_mul_inv, mul_comm]
      _ = (Real.sqrt ((D.m z : ℝ) / c)) ^ 2 := hsqrt.symm
      _ = _ := by rw [pow_two]
  have hcoefC :
      (((c⁻¹ : ℝ) : ℂ) * (D.m z : ℂ)) =
        (((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) *
          ((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ)) := by
    exact_mod_cast hcoefR
  simp only [simpleOnLineSynthesis]
  rw [star_mul']
  rw [hreal]
  simp only [Complex.star_def, Complex.conj_ofReal]
  calc
    (((c⁻¹ : ℝ) : ℂ) *
        ((D.m z : ℂ) * (D.v z k * D.v z l))) =
      ((((c⁻¹ : ℝ) : ℂ) * (D.m z : ℂ)) *
        (D.v z k * D.v z l)) := by ring
    _ =
      ((((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) *
          ((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ)) *
        (D.v z k * D.v z l)) := by rw [hcoefC]
    _ =
      (((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) * D.v z k) *
        (((Real.sqrt ((D.m z : ℝ) / c) : ℝ) : ℂ) * D.v z l) := by
      ring
  intro x
  rfl

end AbstractBlock

section ConcreteZeta

variable (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ)

/-- Auxiliary synthesis for the complete on-line block. -/
def zeroSideOnLineSynthesis
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T)) (OnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) ℂ :=
  onLineSynthesis (Zeta23.ZeroSide.blockData Z T P hconj) (P.a T * P.L T ^ 2)

/-- The article's synthesis matrix: columns are exactly the simple critical-line
zeros in `S₁`. -/
def zeroSideSimpleSynthesis
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T))
      (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) ℂ :=
  simpleOnLineSynthesis (Zeta23.ZeroSide.blockData Z T P hconj) (P.a T * P.L T ^ 2)

/-- The normalized simple critical-line block `P₁`. -/
def zeroSideSimpleP
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  simpleBlockP (Zeta23.ZeroSide.blockData Z T P hconj) (P.a T * P.L T ^ 2)

/-- The normalized multiple critical-line positive block. -/
def zeroSideMultipleP
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  multipleBlockP (Zeta23.ZeroSide.blockData Z T P hconj) (P.a T * P.L T ^ 2)

/-- The article's remainder `Q'`: multiple critical-line zeros plus the
off-line hyperbolic contribution. -/
def zeroSideSimpleQ
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  zeroSideMultipleP Z P T hconj + Zeta23.ZeroSide.hatQ Z T P hconj

/-- The article's Gram matrix `M = VᴴV`. -/
def zeroSideSimpleGram
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Matrix
      (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj))
      (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) ℂ :=
  (zeroSideSimpleSynthesis Z P T hconj).conjTranspose *
    zeroSideSimpleSynthesis Z P T hconj

/-- The simple synthesis has exactly `s₁` columns. -/
theorem card_zeroSideSimpleSynthesis
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Fintype.card (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) =
      Z.s1 T := by
  rw [Zeta23.ZeroSide.s1_eq_mk Z T
    (Zeta23.ZeroSide.evalVec Z T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj)]
  exact card_simpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)

/-- Exact factorization `P₁ = V Vᴴ`. -/
theorem zeroSideSimpleP_eq_synthesis_mul_conjTranspose
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    zeroSideSimpleP Z P T hconj =
      zeroSideSimpleSynthesis Z P T hconj *
        (zeroSideSimpleSynthesis Z P T hconj).conjTranspose := by
  simpa [zeroSideSimpleP, zeroSideSimpleSynthesis] using
    simpleBlockP_eq_simpleOnLineSynthesis_mul_conjTranspose
      (Zeta23.ZeroSide.blockData Z T P hconj) hc

/-- `P₁` is PSD. -/
theorem zeroSideSimpleP_posSemidef
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (zeroSideSimpleP Z P T hconj).PosSemidef := by
  exact simpleBlockP_posSemidef (Zeta23.ZeroSide.blockData Z T P hconj) hc

/-- The multiple critical-line positive remainder is PSD. -/
theorem zeroSideMultipleP_posSemidef
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (zeroSideMultipleP Z P T hconj).PosSemidef := by
  exact multipleBlockP_posSemidef (Zeta23.ZeroSide.blockData Z T P hconj) hc

/-- `rank P₁ ≤ s₁`. -/
theorem zeroSideSimpleP_rank_le
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (zeroSideSimpleP Z P T hconj).rank ≤ Z.s1 T := by
  rw [Zeta23.ZeroSide.s1_eq_mk Z T
    (Zeta23.ZeroSide.evalVec Z T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj)]
  exact rank_simpleBlockP_le (Zeta23.ZeroSide.blockData Z T P hconj) hc

/-- The multiple positive block has rank at most `s₂`. -/
theorem zeroSideMultipleP_rank_le
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (zeroSideMultipleP Z P T hconj).rank ≤ Z.s2 T := by
  rw [Zeta23.ZeroSide.s2_eq_mk Z T
    (Zeta23.ZeroSide.evalVec Z T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj)]
  exact rank_multipleBlockP_le (Zeta23.ZeroSide.blockData Z T P hconj) hc

/-- The Poisson column bound gives `tr P₁ ≤ s₁`, exactly as in the article. -/
theorem zeroSideSimpleP_rtrace_le
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    rtrace (zeroSideSimpleP Z P T hconj) ≤ (Z.s1 T : ℝ) := by
  rw [Zeta23.ZeroSide.s1_eq_mk Z T
    (Zeta23.ZeroSide.evalVec Z T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj)]
  apply rtrace_simpleBlockP_le (Zeta23.ZeroSide.blockData Z T P hconj) hc
  intro z hz
  exact Zeta23.ZeroSide.sum_normSq_v_le Z T P hconj hreal hPois z
    (mem_onLine_of_mem_S₁ (Zeta23.ZeroSide.blockData Z T P hconj) hz)

/-- The normalized complete positive on-line block splits as `P₁ + P₂`. -/
theorem hatP_eq_simpleP_add_multipleP
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Zeta23.ZeroSide.hatP Z T P hconj =
      zeroSideSimpleP Z P T hconj + zeroSideMultipleP Z P T hconj := by
  simpa [Zeta23.ZeroSide.hatP, zeroSideSimpleP, zeroSideMultipleP] using
    blockP_eq_simpleBlockP_add_multipleBlockP
      (Zeta23.ZeroSide.blockData Z T P hconj) (P.a T * P.L T ^ 2)

/-- The article's exact decomposition `Â = P₁ + Q'`. -/
theorem hat_Az_eq_zeroSideSimpleP_add_zeroSideSimpleQ
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    P.hat T (Z.Az P T) =
      zeroSideSimpleP Z P T hconj + zeroSideSimpleQ Z P T hconj := by
  calc
    P.hat T (Z.Az P T)
        = Zeta23.ZeroSide.hatP Z T P hconj +
            Zeta23.ZeroSide.hatQ Z T P hconj :=
          Zeta23.ZeroSide.hat_Az_eq_hatP_add_hatQ Z T P hconj
    _ = (zeroSideSimpleP Z P T hconj +
          zeroSideMultipleP Z P T hconj) +
          Zeta23.ZeroSide.hatQ Z T P hconj := by
            rw [hatP_eq_simpleP_add_multipleP Z P T hconj]
    _ = zeroSideSimpleP Z P T hconj +
          zeroSideSimpleQ Z P T hconj := by
            simp [zeroSideSimpleQ, add_assoc]

/-- `Q'` is Hermitian. -/
theorem zeroSideSimpleQ_isHermitian
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (zeroSideSimpleQ Z P T hconj).IsHermitian := by
  unfold zeroSideSimpleQ
  exact (zeroSideMultipleP_posSemidef Z P T hconj hc).isHermitian.add
    (Zeta23.ZeroSide.hatQ_isHermitian Z T P hconj)

/-- The article's inertia bound `n₊(Q') ≤ s₂+p`. -/
theorem zeroSideSimpleQ_posIndex_le
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    posIndex (zeroSideSimpleQ_isHermitian Z P T hconj hc) ≤
      Z.s2 T + Z.p T := by
  let hM := zeroSideMultipleP_posSemidef Z P T hconj hc
  let hQ := Zeta23.ZeroSide.hatQ_isHermitian Z T P hconj
  have hadd := RHLinalg.posIndex_add_le hM.isHermitian hQ
  rw [RHLinalg.posIndex_eq_rank_of_posSemidef hM] at hadd
  have hrank := zeroSideMultipleP_rank_le Z P T hconj hc
  have hpos := Zeta23.ZeroSide.posIndex_hatQ_le Z T P hconj hc hQ
  have hbound :
      posIndex (hM.isHermitian.add hQ) ≤ Z.s2 T + Z.p T :=
    hadd.trans (Nat.add_le_add hrank hpos)
  have hcongr :
      posIndex (zeroSideSimpleQ_isHermitian Z P T hconj hc) =
        posIndex (hM.isHermitian.add hQ) := by
    exact Zeta23.ZeroSide.ZeroBlockData.posIndex_congr
      (zeroSideSimpleQ_isHermitian Z P T hconj hc)
      (hM.isHermitian.add hQ)
      (by rfl)
  rw [hcongr]
  exact hbound

/-- The simple Gram matrix is PSD. -/
theorem zeroSideSimpleGram_posSemidef
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    (zeroSideSimpleGram Z P T hconj).PosSemidef := by
  unfold zeroSideSimpleGram
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Spectral defect attached to `P₁`, padded to the exact simple-zero rank
budget `s₁`. -/
def concreteSimplePDefect
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) : ℝ :=
  matrixSpectralDefect
    (zeroSideSimpleP Z P T hconj)
    (zeroSideSimpleP_posSemidef Z P T hconj hc)
    (Z.s1 T)

/-- The matrix spectral defect of `P₁` is exactly the Gram defect of the
article's `M = VᴴV`. -/
theorem concreteSimplePDefect_eq_zeroSideSimpleGramDefect
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    concreteSimplePDefect Z P T hconj hc =
      gramSpectralDefect
        (zeroSideSimpleGram Z P T hconj)
        (zeroSideSimpleGram_posSemidef Z P T hconj) := by
  let V := zeroSideSimpleSynthesis Z P T hconj
  let hPVV := Matrix.posSemidef_self_mul_conjTranspose V
  let hM := Matrix.posSemidef_conjTranspose_mul_self V
  have hfac :
      zeroSideSimpleP Z P T hconj = V * V.conjTranspose := by
    simpa [V] using
      zeroSideSimpleP_eq_synthesis_mul_conjTranspose Z P T hconj hc
  have hcard :
      Fintype.card (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj)) =
        Z.s1 T :=
    card_zeroSideSimpleSynthesis Z P T hconj
  have hroots := gram_nonzero_eigenvalue_multisets_eq V
  have hdef :=
    rootMultisetToDefectBridge_proved
      (V * V.conjTranspose) hPVV
      (V.conjTranspose * V) hM
      hroots
  have hleft :
      concreteSimplePDefect Z P T hconj hc =
        matrixSpectralDefect
          (V * V.conjTranspose) hPVV
          (Fintype.card
            (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj))) := by
    unfold concreteSimplePDefect
    calc
      matrixSpectralDefect
          (zeroSideSimpleP Z P T hconj)
          (zeroSideSimpleP_posSemidef Z P T hconj hc)
          (Z.s1 T)
          =
        matrixSpectralDefect
          (zeroSideSimpleP Z P T hconj)
          (zeroSideSimpleP_posSemidef Z P T hconj hc)
          (Fintype.card
            (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj))) := by
              rw [hcard]
      _ =
        matrixSpectralDefect
          (V * V.conjTranspose) hPVV
          (Fintype.card
            (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj))) := by
              exact matrixSpectralDefect_eq_of_matrix_eq
                (zeroSideSimpleP_posSemidef Z P T hconj hc)
                hPVV _ hfac
  have hgram :
      V.conjTranspose * V = zeroSideSimpleGram Z P T hconj := by
    rfl
  have hright :
      gramSpectralDefect (V.conjTranspose * V) hM =
        gramSpectralDefect
          (zeroSideSimpleGram Z P T hconj)
          (zeroSideSimpleGram_posSemidef Z P T hconj) := by
    exact gramSpectralDefect_eq_of_matrix_eq
      hM (zeroSideSimpleGram_posSemidef Z P T hconj) hgram
  calc
    concreteSimplePDefect Z P T hconj hc
        = matrixSpectralDefect
            (V * V.conjTranspose) hPVV
            (Fintype.card
              (SimpleOnLineColumn (Zeta23.ZeroSide.blockData Z T P hconj))) := hleft
    _ = gramSpectralDefect (V.conjTranspose * V) hM := hdef
    _ = gramSpectralDefect
          (zeroSideSimpleGram Z P T hconj)
          (zeroSideSimpleGram_posSemidef Z P T hconj) := hright

end ConcreteZeta

end HurtadoZeta23
