import HurtadoZeta23.ConcreteCompactOverlapAssembly
import HurtadoZeta23.DirectRedistribution
import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-!
# Lean interface for the computer-assisted seven-point certificate

The Arb/FLINT verifier proves a universal inequality in six nonnegative gaps.
This file contains only the *Lean-side translation* of that statement into
`SevenPointCertificate`.

No kernel-level assumption is introduced here.  The external certificate itself
remains an explicit trust boundary unless it is replayed inside Lean.
-/

/--
Semantic statement corresponding to the archived six-gap certificate.

This is deliberately phrased using the already formalized local functional:
for every seven-point window whose six gaps are nonnegative, `F_p >= delta`.
-/
def ArticleSevenPointInequality : Prop :=
  ∀ (y : ℕ → ℝ) (s : ℕ),
    (∀ j : Fin 6, 0 ≤ windowGap y s j) →
      delta ≤ localFp (limitingWeightOnPoints y) y s

/-- The universal six-gap inequality implies the finite `SevenPointCertificate`. -/
theorem sevenPointCertificate_of_articleSevenPointInequality
    (hcert : ArticleSevenPointInequality)
    {m : ℕ}
    (y : ℕ → ℝ)
    (hmono : ∀ q < m - 1, y q ≤ y (q + 1)) :
    SevenPointCertificate
      (limitingWeightOnPoints y) y m := by
  intro s hs
  apply hcert y s
  intro j
  exact
    windowGap_nonneg
      (m := m) y hmono hs j

/-- Specialization to every actual consecutive retained block. -/
theorem consecutiveSevenPointCertificate_of_article
    (hcert : ArticleSevenPointInequality)
    (T : ℝ)
    (s : ℕ)
    (hs : s + blockLength ≤ articleRetainedCard T)
    (hL : 0 ≤ articleParams.L T) :
    SevenPointCertificate
      (limitingWeightOnPoints
        (consecutiveY T s hs))
      (consecutiveY T s hs)
      blockLength := by
  apply
    sevenPointCertificate_of_articleSevenPointInequality
      hcert
      (consecutiveY T s hs)
  exact
    consecutiveY_mono T s hs hL

/--
Sliding-block form matching `ConcreteCompactOverlapAssembly`.
-/
theorem articleSevenPointCertificates_of_external
    (hcert : ArticleSevenPointInequality)
    (T : ℝ)
    (hS : blockLength ≤ articleRetainedCard T)
    (hL : 0 ≤ articleParams.L T) :
    ∀ s : Fin (articleRetainedCard T - blockLength + 1),
      SevenPointCertificate
        (limitingWeightOnPoints
          (consecutiveY
            T s.1
            (by
              have hs := s.2
              omega)))
        (consecutiveY
          T s.1
          (by
            have hs := s.2
            omega))
        blockLength := by
  intro s
  exact
    consecutiveSevenPointCertificate_of_article
      hcert T s.1
      (by
        have hs := s.2
        omega)
      hL

end HurtadoZeta23
