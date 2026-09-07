import HurtadoZeta23.ArticleSynthesisOverlapBridge
import HurtadoZeta23.ConsecutiveGramRealEntries
import Zeta23.Taper
import Zeta23.ThmD.ParamsD
import Mathlib.Tactic

noncomputable section

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

namespace HurtadoZeta23

/-!
# Exact article synthesis overlap — source-level closure

This replaces the first draft by a smaller proof with three stable layers:

1. an abstract formula for a simple-column Gram entry;
2. the exact `ZeroSide.evalVec` formula on a simple critical-line zero;
3. a direct `Finset.sum_bij` reindexing from `Fin d` to `[0,d-1] ⊂ ℤ`.

The fixed-height positivity hypothesis is the one already present in the
finite article theorem.
-/

/-- Real Fourier transform of the exact Montgomery--Taylor article window. -/
def articleWindowHatR (T r : ℝ) : ℝ :=
  Zeta23.AdmWindow.vHatR (articleParams.phiD T) r

/-- `P.atD T` has exactly the real Fourier transform of `P.phiD T`. -/
theorem article_atD_phiHatR_eq_windowHatR
    (T r : ℝ) :
    (articleParams.atD T).phiHatR T r =
      articleWindowHatR T r := by
  unfold articleWindowHatR
  unfold Zeta23.Params.phiHatR
  unfold Zeta23.Params.phiHat
  unfold Zeta23.AdmWindow.vHatR
  unfold Zeta23.AdmWindow.vHat
  rw [Zeta23.Params.atD_phi_valid T articleParams_valid]

/-- The zero-side normalization `a` is the Input-IV `phiDMean`. -/
theorem article_atD_a_eq_phiDMean
    (T : ℝ) :
    (articleParams.atD T).a T =
      phiDMean
        articleParams.ϱ
        1
        (articleParams.L T)
        articleParams.w := by
  rw [Zeta23.Params.atD_a T articleParams_valid]
  rfl

/--
On a simple critical-line column, the abstract zero-side vector is exactly the
real Fourier transform of the article window at `Im ρ - τ_k`.
-/
theorem articleBlockData_v_eq_windowHatR
    (T : ℝ)
    (z : ArticleSimpleColumn T)
    (k : Fin ((articleParams.atD T).d T)) :
    (ArticleBlockData T).v z.1 k =
      ((articleWindowHatR
          T
          ((articleColumnZero z).im -
            articleParams.tau T (k : ℤ)) : ℝ) : ℂ) := by

  change
    (articleParams.atD T).phiHat T
      (Zeta23.gammaOf (articleColumnZero z) -
        ((articleParams.atD T).tau T (k : ℤ) : ℂ))
      =
    ((articleWindowHatR
        T
        ((articleColumnZero z).im -
          articleParams.tau T (k : ℤ)) : ℝ) : ℂ)

  rw [
    Zeta23.ZeroSide.gammaOf_of_re_eq_half
      (articleSimpleColumn_re_half z)
  ]

  simp only [Zeta23.Params.atD_tau]

  rw [← Complex.ofReal_sub]
  rw [articlePhiHatReal T]
  rw [article_atD_phiHatR_eq_windowHatR]

/--
Abstract simple-column Gram formula.

Because both columns are in `S₁`, their multiplicities are one.  Hence the two
square-root weights contribute exactly `c⁻¹`.
-/
theorem simpleOnLineGram_apply_eq_inv_mul_raw
    {ι d : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    {c : ℝ}
    (hc : 0 < c)
    (i j : SimpleOnLineColumn D) :
    ((simpleOnLineSynthesis D c).conjTranspose *
        simpleOnLineSynthesis D c) i j
      =
    (((c⁻¹ : ℝ) : ℂ) *
      ∑ k : d, D.v i.1 k * D.v j.1 k) := by

  classical

  simp only [
    Matrix.mul_apply,
    Matrix.conjTranspose_apply,
    simpleOnLineSynthesis
  ]

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro k hk

  have hmi :
      D.m i.1 = 1 :=
    mult_eq_one_of_mem_S₁ D i.2

  have hmj :
      D.m j.1 = 1 :=
    mult_eq_one_of_mem_S₁ D j.2

  have hreal :
      star (D.v i.1 k) = D.v i.1 k :=
    conj_v_of_simpleOnLine D i k

  have hreal' :
      (starRingEnd ℂ) (D.v i.1 k) = D.v i.1 k := by
    simpa only [RCLike.star_def] using hreal

  have hsqrt :
      (Real.sqrt (1 / c)) ^ 2 = 1 / c := by
    simpa using
      (sq_sqrt_mult_div (m := 1) hc)

  have hcoefR :
      Real.sqrt (1 / c) * Real.sqrt (1 / c) = c⁻¹ := by
    calc
      Real.sqrt (1 / c) * Real.sqrt (1 / c)
          = (Real.sqrt (1 / c)) ^ 2 := by
              rw [pow_two]
      _ = 1 / c := hsqrt
      _ = c⁻¹ := by simp [one_div]

  have hcoefC :
      (((Real.sqrt (1 / c) : ℝ) : ℂ) *
          ((Real.sqrt (1 / c) : ℝ) : ℂ))
        =
      ((c⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hcoefR

  rw [star_mul']
  rw [hmi, hmj]
  simp only [
    Nat.cast_one,
    Complex.star_def,
    Complex.conj_ofReal
  ]
  rw [hreal']

  calc
    ((Real.sqrt (1 / c) : ℝ) : ℂ) *
          D.v i.1 k *
        (((Real.sqrt (1 / c) : ℝ) : ℂ) * D.v j.1 k)
        =
      (((Real.sqrt (1 / c) : ℝ) : ℂ) *
          ((Real.sqrt (1 / c) : ℝ) : ℂ)) *
        (D.v i.1 k * D.v j.1 k) := by
          ring

    _ =
      ((c⁻¹ : ℝ) : ℂ) *
        (D.v i.1 k * D.v j.1 k) := by
          rw [hcoefC]

/-- The finite `Fin d` overlap before Gram normalization. -/
def articleFiniteOverlapFin
    (T τ τ' : ℝ) : ℝ :=
  ∑ k : Fin ((articleParams.atD T).d T),
    articleWindowHatR
        T
        (τ - articleParams.tau T (k : ℤ)) *
      articleWindowHatR
        T
        (τ' - articleParams.tau T (k : ℤ))

/--
The concrete global simple Gram entry is the finite real overlap divided by
`a L²`.
-/
theorem articleGlobalSimpleGram_re_eq_finiteOverlap
    {T : ℝ}
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (i j : ArticleSimpleColumn T) :
    (articleGlobalSimpleGram T i j).re
      =
    articleFiniteOverlapFin
        T
        (articleColumnZero i).im
        (articleColumnZero j).im
      /
    ((articleParams.atD T).a T *
      (articleParams.atD T).L T ^ 2) := by

  let c : ℝ :=
    (articleParams.atD T).a T *
      (articleParams.atD T).L T ^ 2

  have hc' : 0 < c := by
    simpa [c] using hc

  have hraw :
      articleGlobalSimpleGram T i j
        =
      (((c⁻¹ : ℝ) : ℂ) *
        ∑ k : Fin ((articleParams.atD T).d T),
          (ArticleBlockData T).v i.1 k *
            (ArticleBlockData T).v j.1 k) := by

    change
      (((simpleOnLineSynthesis
            (ArticleBlockData T)
            c).conjTranspose *
          simpleOnLineSynthesis
            (ArticleBlockData T)
            c) i j)
        =
      (((c⁻¹ : ℝ) : ℂ) *
        ∑ k : Fin ((articleParams.atD T).d T),
          (ArticleBlockData T).v i.1 k *
            (ArticleBlockData T).v j.1 k)

    exact
      simpleOnLineGram_apply_eq_inv_mul_raw
        (ArticleBlockData T)
        hc'
        i j

  have hsum :
      (∑ k : Fin ((articleParams.atD T).d T),
          (ArticleBlockData T).v i.1 k *
            (ArticleBlockData T).v j.1 k)
        =
      ((articleFiniteOverlapFin
          T
          (articleColumnZero i).im
          (articleColumnZero j).im : ℝ) : ℂ) := by

    unfold articleFiniteOverlapFin

    simp_rw [
      articleBlockData_v_eq_windowHatR T i,
      articleBlockData_v_eq_windowHatR T j
    ]

    push_cast
    rfl

  have hcomplex :
      articleGlobalSimpleGram T i j
        =
      (((c⁻¹ *
          articleFiniteOverlapFin
            T
            (articleColumnZero i).im
            (articleColumnZero j).im : ℝ) : ℂ)) := by
    calc
      articleGlobalSimpleGram T i j
          =
        (((c⁻¹ : ℝ) : ℂ) *
          ∑ k : Fin ((articleParams.atD T).d T),
            (ArticleBlockData T).v i.1 k *
              (ArticleBlockData T).v j.1 k) := hraw

      _ =
        (((c⁻¹ : ℝ) : ℂ) *
          ((articleFiniteOverlapFin
            T
            (articleColumnZero i).im
            (articleColumnZero j).im : ℝ) : ℂ)) := by
              rw [hsum]

      _ =
        (((c⁻¹ *
          articleFiniteOverlapFin
            T
            (articleColumnZero i).im
            (articleColumnZero j).im : ℝ) : ℂ)) := by
              norm_cast

  rw [hcomplex]
  simp only [Complex.ofReal_re]

  change
    c⁻¹ *
        articleFiniteOverlapFin
          T
          (articleColumnZero i).im
          (articleColumnZero j).im
      =
    articleFiniteOverlapFin
        T
        (articleColumnZero i).im
        (articleColumnZero j).im / c

  rw [div_eq_mul_inv]
  ring

/--
Direct reindexing of a `Fin d` sum as the literal integer interval
`[0,d-1]`.  No auxiliary embedding is needed.
-/
theorem sum_fin_eq_retainedIndexSet
    {d : ℕ}
    (f : ℤ → ℝ) :
    (∑ k : Fin d, f (k : ℤ))
      =
    Finset.sum
      (retainedIndexSet (0 : ℤ) (Int.ofNat d - 1))
      f := by

  classical

  change
    Finset.sum
        (Finset.univ : Finset (Fin d))
        (fun k => f (k : ℤ))
      =
    Finset.sum
      (retainedIndexSet (0 : ℤ) (Int.ofNat d - 1))
      f

  unfold retainedIndexSet

  apply
    Finset.sum_bij
      (fun (k : Fin d) (_ : k ∈ (Finset.univ : Finset (Fin d))) =>
        ((k.1 : ℕ) : ℤ))

  · intro k hk
    simp only [Finset.mem_Icc]
    constructor
    · exact Int.natCast_nonneg _
    ·
      have hkltZ :
          ((k.1 : ℕ) : ℤ) < (d : ℤ) := by
        exact_mod_cast k.2

      change
        ((k.1 : ℕ) : ℤ) ≤ (d : ℤ) - 1

      omega

  · intro a ha b hb hab
    apply Fin.ext
    exact Int.ofNat.inj hab

  · intro k hk
    simp only [Finset.mem_Icc] at hk

    have hk0 :
        0 ≤ k :=
      hk.1

    have hkUpper :
        k ≤ (d : ℤ) - 1 := by
      simpa using hk.2

    have hkltZ :
        k < (d : ℤ) := by
      omega

    have hkcast :
        ((k.toNat : ℕ) : ℤ) = k := by
      rw [Int.ofNat_toNat]
      exact max_eq_left hk0

    have hkltCast :
        ((k.toNat : ℕ) : ℤ) < (d : ℤ) := by
      rw [hkcast]
      exact hkltZ

    have hklt :
        k.toNat < d := by
      exact_mod_cast hkltCast

    refine
      ⟨⟨k.toNat, hklt⟩,
       Finset.mem_univ _,
       ?_⟩

    exact hkcast

  · intro k hk
    rfl

/--
The finite synthesis overlap is literally the finite integer-lattice overlap
used by Input IV.
-/
theorem articleFiniteOverlapFin_eq_intervalFiniteGridOverlap
    (T τ τ' : ℝ) :
    articleFiniteOverlapFin T τ τ'
      =
    intervalFiniteGridOverlap
      articleParams.ϱ
      1
      (articleParams.L T)
      articleParams.w
      T
      τ
      τ'
      0
      (articleLastGridIndex T) := by

  unfold articleFiniteOverlapFin
  unfold intervalFiniteGridOverlap

  have hlast :
      Int.ofNat ((articleParams.atD T).d T) - 1
        =
      articleLastGridIndex T := by
    unfold articleLastGridIndex
    simp only [Zeta23.Params.atD_d]

  rw [
    sum_fin_eq_retainedIndexSet
      (d := (articleParams.atD T).d T)
      (fun k =>
        articleWindowHatR
          T
          (τ - articleParams.tau T k) *
        articleWindowHatR
          T
          (τ' - articleParams.tau T k))
  ]

  rw [hlast]

  apply Finset.sum_congr rfl
  intro k hk

  unfold articleWindowHatR
  unfold phiDGridSummand
  unfold Zeta23.Params.phiD
  unfold Zeta23.Params.tau
  unfold Zeta23.Params.hgrid
  unfold articleParams

  rfl

/--
Closed fixed-height synthesis/finite-overlap identity.
-/
theorem consecutiveGramBlock_re_eq_normalizedIntervalOverlap
    {T : ℝ}
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    (consecutiveGramBlock T s hs i j).re
      =
    normalizedIntervalOverlap
      articleParams.ϱ
      (articleParams.L T)
      articleParams.w
      T
      (consecutiveZero T s hs i).im
      (consecutiveZero T s hs j).im
      0
      (articleLastGridIndex T) := by

  rw [consecutiveGramBlock_apply]

  rw [
    articleGlobalSimpleGram_re_eq_finiteOverlap
      hc
      (consecutiveSimpleColumn T s hs i)
      (consecutiveSimpleColumn T s hs j)
  ]

  rw [
    articleFiniteOverlapFin_eq_intervalFiniteGridOverlap
  ]

  unfold normalizedIntervalOverlap

  rw [article_atD_a_eq_phiDMean T]

  simp only [Zeta23.Params.atD_L]

  rfl

/-- Symmetry of the normalized finite overlap in its two ordinate arguments. -/
theorem normalizedIntervalOverlap_swap
    (T τ τ' : ℝ) :
    normalizedIntervalOverlap
        articleParams.ϱ
        (articleParams.L T)
        articleParams.w
        T
        τ
        τ'
        0
        (articleLastGridIndex T)
      =
    normalizedIntervalOverlap
        articleParams.ϱ
        (articleParams.L T)
        articleParams.w
        T
        τ'
        τ
        0
        (articleLastGridIndex T) := by

  unfold normalizedIntervalOverlap
  unfold intervalFiniteGridOverlap

  apply congrArg
    (fun x : ℝ =>
      x /
        (phiDMean
            articleParams.ϱ
            1
            (articleParams.L T)
            articleParams.w *
          articleParams.L T ^ 2))

  apply Finset.sum_congr rfl
  intro k hk

  unfold phiDGridSummand
  ring

/--
Orientation required by the original Input-IV bridge: `(j,i)`, so that the
limiting variable is `y_j-y_i`.
-/
theorem consecutiveGramBlock_re_eq_normalizedIntervalOverlap_rev
    {T : ℝ}
    (hc :
      0 <
        (articleParams.atD T).a T *
          (articleParams.atD T).L T ^ 2)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (i j : Fin blockLength) :
    (consecutiveGramBlock T s hs i j).re
      =
    normalizedIntervalOverlap
      articleParams.ϱ
      (articleParams.L T)
      articleParams.w
      T
      (consecutiveZero T s hs j).im
      (consecutiveZero T s hs i).im
      0
      (articleLastGridIndex T) := by

  rw [
    consecutiveGramBlock_re_eq_normalizedIntervalOverlap
      hc s hs i j
  ]

  exact
    normalizedIntervalOverlap_swap
      T
      (consecutiveZero T s hs i).im
      (consecutiveZero T s hs j).im

end HurtadoZeta23
