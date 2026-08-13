# A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function

This repository contains the manuscript and reproducibility artifacts
for

> **A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta
> Function**

by **Michael Hurtado**.

The paper proves the unconditional lower bound

$$
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge
0.6730732086087052768351\ldots
$$

for the proportion of simple zeros of the Riemann zeta function on the
critical line.

The new ingredient is a **nonuniform position-weighted refinement** of a
seven-point stability/local-to-global argument.

------------------------------------------------------------------------

## Main result

Let

\[ H\_{`\rm MT`{=tex}} =
`\frac32`{=tex}-`\frac1{\sqrt2}`{=tex}`\cot`{=tex}`\frac1{\sqrt2}`{=tex}.
\]

The manuscript establishes

\[ `\liminf`{=tex}\_{T`\to`{=tex}`\infty`{=tex}}
`\frac{N_0^s(T,2T)}{N(T,2T)}`{=tex} `\ge`{=tex}
`\frac{655000H_{\rm MT}-1305}{652504}`{=tex} =
0.6730732086087052768351`\ldots `{=tex}. \]

The computer-assisted component uses the position-dependent pressure
vector

\[ p= `\frac{1}{10^7}`{=tex} (2714,3733,3553,3553,3733,2714), \]

which satisfies

\[ `\sum`{=tex}\_{j=1}\^{6}p_j=`\frac1{500}`{=tex}, \]

together with the certified seven-point inequality

\[ F\_{6,`\mathrm{nonuniform}`{=tex}} `\ge`{=tex}
`\frac{39}{10000}`{=tex}. \]

The final local-to-global argument uses block length

\[ m=262. \]

------------------------------------------------------------------------

## Repository structure

``` text
.
├── README.md
├── CITATION.cff
├── LICENSE-CODE
├── LICENSE-CONTENT
│
├── paper/
│   ├── main.tex
│   └── main.pdf
│
├── certification/
│   └── arb_256/
│       ├── README.md
│       ├── certify_nonuniform_3900_v1_1.py
│       ├── run_certificate_256.ps1
│       ├── run_certificate_256.sh
│       ├── arb-certificate-256.log
│       ├── certificate-summary.json
│       ├── environment-256.txt
│       ├── requirements-lock-256.txt
│       ├── verifier-sha256-256.txt
│       ├── certificate-log-sha256-256.txt
│       └── SHA256SUMS.txt
│
└── docs/
```

### `paper/`

Contains the submission-ready LaTeX source and compiled manuscript.

### `certification/arb_256/`

Contains the complete computer-assisted proof artifact for the
nonuniform seven-point certificate.

See [`certification/arb_256/README.md`](certification/arb_256/README.md)
for exact reproduction instructions.

------------------------------------------------------------------------

## Reproducibility releases

Two releases play distinct roles.

### Manuscript

**`v1.1.0-paper`**

This release freezes the submission-ready manuscript.

### Computational artifact

**`v1.0.0-paper`**

Commit:

``` text
c57f53e
```

This earlier immutable release freezes the computational artifact used
by the manuscript.

The separation is intentional:

``` text
v1.1.0-paper
    │
    └── submission-ready manuscript
             │
             ▼
v1.0.0-paper @ c57f53e
    │
    └── frozen Arb/FLINT certificate
             │
             ▼
      256-bit verification
             │
             ▼
 F6_nonuniform >= 39/10000
```

Subsequent changes to the repository's default branch are not part of
the trust base of the frozen computational certificate.

------------------------------------------------------------------------

## 256-bit certificate

The archived certification run uses:

  Parameter                       Value
  ------------------- -----------------
  Grid denominator               `4000`
  Working precision          `256 bits`
  Initial boxes                  `1296`
  Visited nodes             `1,119,372`
  Splits                      `559,038`
  Pruned nodes                `560,334`
  Maximum depth                    `39`
  Status                `verified=true`

The certified pressure vector is

``` text
(2714, 3733, 3553, 3553, 3733, 2714) / 10^7
```

and the certified target is

``` text
F6_nonuniform >= 39/10000
```

------------------------------------------------------------------------

## Verification hashes

The frozen verifier has SHA-256

``` text
8eb7b4a17da8e114881264d3c2fc8daf262a0558d4248692b386c0fca2cc4301
```

and the archived 256-bit certification log has SHA-256

``` text
4b0e62dcb5c4014504981f16e431144e3a01184b2aa2aa6b0bf650705d59db83
```

The complete hash manifest is available at

``` text
certification/arb_256/SHA256SUMS.txt
```

These hashes allow the verifier and archived execution log used by the
paper to be checked independently.

------------------------------------------------------------------------

## Reproducing the certificate

The archived computation uses Python and `python-flint`/FLINT-Arb
directed interval arithmetic.

The recorded reference environment uses:

``` text
Python 3.14.7
python-flint 0.9.0
```

For the complete procedure, see:

``` text
certification/arb_256/README.md
```

Linux/macOS users may use:

``` bash
cd certification/arb_256
bash run_certificate_256.sh
```

Windows PowerShell users may use:

``` powershell
cd certification/arb_256
.\run_certificate_256.ps1
```

A successful execution must terminate with

``` text
verified=true
```

The verifier should not be modified between hash verification and
execution.

------------------------------------------------------------------------

## Trust model

The computer-assisted proposition is not claimed to be formally verified
in a proof assistant.

Its computational trust base includes:

-   the frozen verifier;
-   `python-flint`;
-   FLINT/Arb and its dependencies;
-   the execution environment;
-   the correctness of directed interval arithmetic implemented by those
    libraries.

The archived 128-bit and 256-bit executions are replications of the same
verification algorithm at different working precisions. They should not
be interpreted as algorithmically independent proof implementations.

The analytic and finite-dimensional arguments connecting the certified
seven-point inequality to the main theorem are given in the manuscript.

------------------------------------------------------------------------

## Relation to previous work

The manuscript distinguishes the present contribution from the
immediately preceding reproducible artifacts.

The upstream work of **Sunghyeon Jo** introduced the relevant
reproducible seven-point stability framework with a uniform pressure and
certified

\[ `\frac{19}{5000}`{=tex}=0.0038, \]

leading to the bound

\[ 0.6730085279277797`\ldots `{=tex}. \]

A subsequent reproducible refinement by **Lea Rademacher** strengthened
the uniform seven-point certificate to

\[ `\frac{191}{50000}`{=tex}=0.00382, \]

leading to

\[ 0.6730213619501665`\ldots `{=tex}. \]

The present work keeps the same total pressure

\[ `\sum `{=tex}p_j=`\frac1{500}`{=tex}, \]

but allows its distribution among the six gap positions to vary. The
certified nonuniform vector raises the local value to

\[ `\frac{39}{10000}`{=tex}=0.0039. \]

The precise mathematical and bibliographic comparison is given in the
manuscript.

------------------------------------------------------------------------

## AI provenance

Recent upstream computational artifacts relevant to this project report
the use of AI systems during their development.

The present repository treats AI use as **research provenance rather
than mathematical authorship**.

All mathematical claims in the manuscript are intended to be supported
by explicit arguments, cited external results, or reproducible
computational certificates. The computer-assisted component is
accompanied by source code, execution logs, cryptographic hashes,
machine-readable parameters, and reproduction instructions so that it
can be independently inspected.

------------------------------------------------------------------------

## Citation

If you use the mathematical result, please cite the accompanying
manuscript.

If you use or reproduce the computational artifact, please also cite the
repository/release.

Citation metadata is provided in:

``` text
CITATION.cff
```

The submission-ready manuscript is frozen in:

``` text
v1.1.0-paper
```

and the computational artifact used by the manuscript is frozen in:

``` text
v1.0.0-paper @ c57f53e
```

------------------------------------------------------------------------

## License

Different parts of this repository are released under licenses
appropriate to their content.

### Source code

Unless otherwise stated, source code in this repository, including the
Arb/FLINT certificate verifier and reproduction scripts, is released
under the **MIT License**.

See:

``` text
LICENSE-CODE
```

### Manuscript, documentation, and reproducibility data

The manuscript, documentation, certificate metadata, execution logs, and
other non-software material are released under the **Creative Commons
Attribution 4.0 International License (CC BY 4.0)**.

See:

``` text
LICENSE-CONTENT
```

Third-party software and dependencies retain their respective licenses.

------------------------------------------------------------------------

## Author

**Michael Hurtado**

Repository:

`https://github.com/MichaelMobius/simple_zeros_of_the_riemann_zeta_function`

------------------------------------------------------------------------

## Status

**Current manuscript release:** `v1.1.0-paper`

**Frozen computational artifact:** `v1.0.0-paper @ c57f53e`

**Certificate status:** `verified=true`

**Working precision:** `256 bits`

**Certified local bound:** `39/10000`

**Resulting unconditional bound:**

\[ 0.6730732086087052768351`\ldots`{=tex} \]
