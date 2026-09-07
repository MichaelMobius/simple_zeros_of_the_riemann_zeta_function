import HurtadoZeta23.SevenPointCertificateBridge

noncomputable section

namespace HurtadoZeta23

/-!
# External Arb/FLINT certificate frontier

The archived verifier checks the six-gap inequality underlying
`ArticleSevenPointInequality` at 256-bit Arb precision.

This file intentionally contains no theorem of type
`ArticleSevenPointInequality`: a successful external log is not a Lean proof
term.  Keeping the proposition named here makes the trust boundary explicit
until either:
1. the interval certificate is replayed in Lean, or
2. the final artifact deliberately declares the Arb verifier as an external
   trusted component.
-/

/-- Exact mathematical statement certified by the external Arb/FLINT run. -/
abbrev ArchivedSevenPointClaim : Prop :=
  ArticleSevenPointInequality

/-- Human-readable verifier SHA-256, kept as data rather than as a logical axiom. -/
def archivedVerifierSHA256 : String :=
  "8eb7b4a17da8e114881264d3c2fc8daf262a0558d4248692b386c0fca2cc4301"

/-- Human-readable 256-bit log SHA-256. -/
def archivedCertificateLogSHA256 : String :=
  "4b0e62dcb5c4014504981f16e431144e3a01184b2aa2aa6b0bf650705d59db83"

end HurtadoZeta23
