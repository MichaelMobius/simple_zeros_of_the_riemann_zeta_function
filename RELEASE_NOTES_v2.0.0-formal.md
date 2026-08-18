# v2.0.0-formal

This release consolidates the mathematical manuscript, the proof-carrying
finite certificates, and the end-to-end Lean formalization.

## Highlights

- Unconditional bound:
  `0.6730732086087052768351...`
- Position-weighted pressure:
  `(2714,3733,3553,3553,3733,2714)/10^7`
- Certified local seven-point lower bound:
  `39/10000`
- Block length:
  `262`
- Arb/FLINT proof-carrying certificate v1.2
- exact q60 integer replay v1.3
- complete Lean endpoint:
  `HurtadoZeta23.article_main_internal`
- 1,119,372-node tree replay
- 190,953 tangent leaves
- 1,296 surviving prefilter boxes proved sound
- no local `sorry`, `admit`, or mathematical `axiom` declarations in the audited release tree

## Trust note

Large finite Lean checks use `native_decide`; the release therefore includes
Lean's native evaluation mechanism in its computational trust base.  Arb/FLINT
is retained as independent provenance/cross-checking and is no longer an
assumed premise of the final Lean theorem.

## Historical releases

Earlier `v1.x` releases remain historical snapshots of the manuscript and
Arb-based computational artifact.  They should be retained.
