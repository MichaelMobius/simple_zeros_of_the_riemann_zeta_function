# A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function

This repository contains the manuscript, finite certificates, and Lean 4
formalization for

> **A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function**  
> Michael Hurtado

## Main result

The manuscript proves the unconditional lower bound

\[
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
\frac{655000H_{\mathrm{MT}}-1305}{652504}
=
0.6730732086087052768351\ldots,
\]

where

\[
H_{\mathrm{MT}}
=
\frac32-\frac1{\sqrt2}\cot\!\left(\frac1{\sqrt2}\right).
\]

The position-dependent pressure vector is

\[
p=\frac1{10^7}(2714,3733,3553,3553,3733,2714),
\qquad
\sum_{j=1}^6 p_j=\frac1{500},
\]

and the certified seven-point lower bound is

\[
\mathcal F_p(g)\ge \frac{39}{10000}.
\]

The final block length is \(m=262\).

## Verification status

The finite seven-point argument is available in three mutually checking layers.

1. **Arb/FLINT proof-carrying certificate v1.2.**  
   Rigorous interval bounds and the complete branch-and-bound tree are generated
   with `python-flint`.  A separate standard-library-only checker replays the
   complete finite certificate without importing Arb.

2. **Fixed-point q60 certificate v1.3.**  
   All exported bounds are conservatively normalized to scale \(2^{60}\).
   The checker uses integer arithmetic only and replays the same tree, including
   exact Bareiss/Sylvester Hessian checks.

3. **Lean 4 end-to-end formalization.**  
   The Lean development proves the analytic/transcendental bridge required by
   the certificate (including rational enclosures for the kernel and its
   derivatives), the q60 second-derivative table soundness, line/path calculus,
   the fixed \(6\times6\) Sylvester bridge, all tangent records, the complete
   packed tree replay, the seven-point inequality, and the final asymptotic
   theorem.

The final endpoint is:

```lean
HurtadoZeta23.article_main_internal
```

The audited source tree contains no local `sorry`, `admit`, or locally declared
mathematical `axiom`.  Several large finite checks use Lean's `native_decide`.
Accordingly, the computational trusted base includes Lean's native evaluation
mechanism; this repository does **not** describe the current implementation as
a purely kernel-reduction-only certificate.

## Certificate statistics

The v1.3 fixed-point replay reports:

| item | count |
|---|---:|
| initial boxes | 1,296 |
| nodes | 1,119,372 |
| splits | 559,038 |
| pressure leaves | 5,269 |
| interval leaves | 364,112 |
| tangent leaves | 190,953 |
| maximum depth | 39 |

Minimum post-quantization margins:

- interval leaves: `5.598149478924466e-10`
- tangent leaves: `2.9986027445962243e-09`

Principal v1.3 file hashes:

| file | SHA-256 |
|---|---|
| `kernel_q60.i64` | `a16cce93ee3ffeab9c1242f9cee1636d7de5843f20c2c4c894cc04ae1f37740a` |
| `second_q60.i64` | `5a460c9f44b16d13d9ebee5ebe8f37c0caac6f4f5befb15476a49255d08376f6` |
| `tangent_q60.i64` | `6d7c646217dc27a6ebfed3c9eaeb00dee3446032ed6825abff215888ebbb60df` |
| `tree_4bit.bin` | `edc7778018342d35d81b1d98d22e2f4c873dd6bce7bf86f1b4d20837cdf7984a` |

The Lean `sharp` kernel table deliberately weakens cells `0..2800`; every
modified value is no larger than the archived q60 lower bound.  An independent
integer-only replay with this weakened table was also audited successfully.
See `audit/FINAL_ADVERSARIAL_AUDIT.md`.

## Repository layout

```text
.
├── README.md
├── CITATION.cff
├── RELEASE_NOTES_v2.0.0-formal.md
├── paper/
│   ├── main.tex
│   └── main.pdf
├── formalization/
│   ├── README.md
│   ├── lean-toolchain
│   └── HurtadoZeta23/
├── certification/
│   ├── arb_v1_2/
│   └── fixedpoint_v1_3/
├── audit/
│   ├── FINAL_ADVERSARIAL_AUDIT.md
│   └── README.md
└── docs/
    ├── FORMALIZATION.md
    ├── TRUST_MODEL.md
    ├── REPRODUCIBILITY.md
    └── RELEASE_CHECKLIST.md
```

The historical `certification/arb_256/` directory already present in the
repository may be retained as an earlier reproducibility snapshot.

## Reproducing the finite certificates

### Arb/FLINT v1.2

```powershell
cd certification\arb_v1_2
python .\check_seven_point_certificate.py .\seven-point-cert
```

The archived check must end with all of the following true:

```text
certificate_structure_valid
prefilter_replayed
all_leaves_verified
tree_complete
```

and `arb_imported=false`.

To regenerate v1.2 from rigorous Arb arithmetic:

```powershell
python .\certify_nonuniform_3900_v1_2.py `
  --precision 256 `
  --progress-every 100000 `
  --emit-certificate .\seven-point-cert
```

The archived v1.2 generation environment records CPython 3.12.13 and
`python-flint==0.9.0`.

### Fixed-point v1.3

```powershell
cd certification\fixedpoint_v1_3
python .\check_fixedpoint_certificate.py .\seven-point-fixed
```

The checker is integer-only and requires no Arb, `python-flint`, NumPy,
floating-point arithmetic, or external solver.

## Reproducing the Lean formalization

The source snapshot was compile-confirmed with Lean `v4.33.0-rc2` against the
project's pinned Zeta23 dependency.  Before tagging a release, run
`FINALIZE_FORMAL_RELEASE.ps1`; it copies the exact Lake configuration from the
working Lean project, records the upstream Zeta23 remote/commit, performs a
clean build, and archives `#print axioms` output.

See:

- `formalization/README.md`
- `docs/REPRODUCIBILITY.md`
- `docs/TRUST_MODEL.md`

## Release

The intended consolidated release tag is:

```text
v2.0.0-formal
```

Earlier manuscript/computational releases remain useful historical snapshots
and should not be deleted.

## AI provenance

AI systems were used during research and formalization workflows.  They are
treated as research provenance, not mathematical authorship.  The mathematical
claim is supported by the manuscript, reproducible finite certificates, and
the Lean formalization.

## License

Retain the repository's existing licensing split:

- source code: `LICENSE-CODE`;
- manuscript, documentation, certificate metadata, and reproducibility data:
  `LICENSE-CONTENT`;
- third-party dependencies retain their own licenses.

## Author

Michael Hurtado

Repository:
`https://github.com/MichaelMobius/simple_zeros_of_the_riemann_zeta_function`
