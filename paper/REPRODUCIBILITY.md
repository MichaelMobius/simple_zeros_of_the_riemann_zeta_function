# Reproducibility snapshot

This file records the exact manuscript and formal-verification objects used for
the current article.

## Manuscript

- Source commit: `0b56c61d93b0020351d66ca745d0c3a2de1faee7`
- PDF regeneration commit: `588b3cf114fa50b1766e702321d6315241b2ba15`
- `paper/main.tex` Git blob: `64d28a5aa09e1cc6d8955b12eba65fc8e9fa0499`
- `paper/main.pdf` Git blob: `e6b82c240e9b42129dcd860f357211bbd43c0025`
- PDF build workflow run: `35676850584` — success
- The PDF workflow also checks for LaTeX errors, overfull boxes, and unresolved
  citations or cross-references before committing `main.pdf`.

## Formal theorem

- Project theorem snapshot:
  `e0f67e112f59b31a4278e1d56377f5e4f1628836`
- Literal endpoint:
  [
  C_{\rm pub}\le
  \liminf_{T\to\infty}
  \frac{N_0^s(T,2T)}{N(T,2T)},
  qquad
  C_{\rm pub}
  =
  \frac{1125000H_{\rm MT}-2220}{1120671}.
  ]
- Exact axiom-whitelist workflow run:
  `35610878605` — success
- Required transitive axiom closure:
  `propext, Classical.choice, Quot.sound`
- `sorryAx` is rejected by CI.

## Pinned formal environment

- Anthropic `formal-math`:
  `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`
- Lean:
  `leanprover/lean4:v4.33.0-rc2`
- mathlib:
  `51e6992efd06126df61a496bebf8f49482a4e129`

## Exact finite certificate

The checked chain is

`44100 -> 511 -> 231 -> 23 -> 5 -> contradiction`.

The three bootstrap rounds satisfy

- `511 = 280 + 231`
- `231 = 208 + 23`
- `23 = 18 + 5`

with 190, 2433, and 246 distinct one-variable minorant cells respectively.

The five terminal words are

`121212, 121221, 122121, 212121, 212212`.

Their exact final margins above `39/10000` are:

- `121212` and `212121`:
  `1191001492104159283646995579 / 1821262686688912135146560000000000`
- `121221` and `122121`:
  `122261493153092324461322292173429 / 136541153466195789306295504800000000000`
- `212212`:
  `10429603649012763691 / 1397723775304050000000000`

All five margins are greater than `1/2000000`.

## Independent interval check

The Arb/FLINT reproduction of the seven-point inequality is stored under
`certification/arb_256`.  It is independent of the Lean theorem path and is
retained as a separate reproducibility check.
