#!/usr/bin/env python3
"""Generate the validated v17 manuscript and metadata.

The transformation is fail-closed on the original audited v16 source, but is
also idempotent after v17 has already been promoted on the review branch.
"""
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parents[2]
FRAG = Path(__file__).resolve().parent
EXPECTED_V16_BLOB = "6bbaf51eeab527ec5f1c35bd4bdb1bb2cfb6476e"
V17_HEADER = "% Manuscript version v17: pressure-preserving averaging and adjacent-pair refinement."
NEW_DECIMAL = "0.6731175265883904388096"
NEW_DECIMAL_LONG = "0.6731175265883904388095857434"


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def repl(text: str, pattern: str, replacement: str, label: str, flags=re.S) -> str:
    out, n = re.subn(pattern, lambda _: replacement, text, count=1, flags=flags)
    if n != 1:
        raise RuntimeError(f"{label}: expected 1 replacement, got {n}")
    return out


def frag(name: str) -> str:
    return (FRAG / name).read_text(encoding="utf-8").rstrip()


def assert_v17(text: str) -> None:
    required = [
        V17_HEADER,
        r"\frac{1125000H_{\rm MT}-2220}{1120671}",
        r"\label{prop:blockstab450}",
        r"\frac{6363}{30868750}",
        r"\label{eq:pressure-global}",
    ]
    missing = [marker for marker in required if marker not in text]
    if missing:
        raise RuntimeError(f"existing v17 source is missing required markers: {missing}")


def clean_v17_text(text: str) -> str:
    # Editorial cleanup: this compound phrase produced the only inherited
    # overfull hbox in the validated v17 build.
    text = text.replace("functional-equation/conjugation", "functional-equation and conjugation")
    return text


def transform_v16(text: str) -> str:
    text = repl(
        text,
        r"% Manuscript version v16:[^\n]*",
        V17_HEADER,
        "version",
        flags=0,
    )
    text = repl(
        text,
        r"\\title\{[^{}]*\}",
        r"\title{Pressure-preserving refinements for simple zeros of the Riemann zeta function}",
        "title",
        flags=0,
    )
    text = repl(text, r"\\date\{[^{}]*\}", r"\date{September 6, 2026}", "date", flags=0)
    text = repl(text, r"\\begin\{abstract\}.*?\\end\{abstract\}", frag("abstract.tex"), "abstract")
    text = repl(
        text,
        r"The contribution of the present paper is narrower and explicit\..*?"
        r"After global redistribution and shifted-block averaging, the block length\s*"
        r"\\\(m=262\\\) yields the theorem below\.",
        frag("intro.tex"),
        "intro",
    )
    text = repl(
        text,
        r"\\begin\{theorem\}\[Main theorem\]\\label\{thm:main\}.*?\\end\{theorem\}",
        frag("theorem.tex"),
        "theorem",
    )
    text = repl(
        text,
        r"\\paragraph\{Priority convention\.\}.*?(?=\\section\{The common finite compression)",
        frag("priority.tex") + "\n\n",
        "priority",
    )
    text = repl(
        text,
        r"\\begin\{proposition\}\[Pressure redistribution\]\\label\{prop:redist\}.*?\\end\{proof\}",
        frag("redist.tex"),
        "redistribution",
    )
    text = repl(
        text,
        r"\\begin\{corollary\}\\label\{cor:energy\}.*?(?=\\section\{Comparison and structural interpretation\})",
        frag("core.tex") + "\n\n",
        "block core",
    )
    text = repl(
        text,
        r"\\section\{Comparison and structural interpretation\}.*?(?=\\section\{Scope and trust base\})",
        frag("comparison.tex") + "\n\n",
        "comparison",
    )
    anchor = "Proposition~\\ref{prop:cert} is computer-assisted.  Its trust base includes the"
    i = text.find(anchor)
    if i < 0:
        raise RuntimeError("trust anchor not found")
    j = text.find("\n\n", i)
    if j < 0:
        raise RuntimeError("trust paragraph end not found")
    text = text[: j + 2] + frag("trust.tex") + "\n\n" + text[j + 2 :]
    text = repl(
        text,
        r"\\section\{Exact arithmetic\}.*?(?=\\begin\{thebibliography\})",
        frag("exact.tex") + "\n\n",
        "exact arithmetic",
    )
    return clean_v17_text(text)


def patch_main() -> None:
    src = ROOT / "paper/main.tex"
    data = src.read_bytes()
    blob = git_blob_sha1(data)
    text = data.decode("utf-8")

    if blob == EXPECTED_V16_BLOB:
        text = transform_v16(text)
        mode = "v16_to_v17"
    elif text.startswith(V17_HEADER):
        assert_v17(text)
        text = clean_v17_text(text)
        mode = "v17_idempotent"
    else:
        raise RuntimeError(
            "paper/main.tex is neither the audited v16 source nor a validated v17 source\n"
            f"observed git blob SHA1: {blob}"
        )

    assert_v17(text)
    out = ROOT / "paper/main_v17.tex"
    out.write_text(text, encoding="utf-8")
    print("generation_mode", mode)
    print("source_git_blob_sha1", blob)
    print("main_v17_sha256", hashlib.sha256(text.encode()).hexdigest())


def normalize_readme(text: str) -> str:
    text = text.replace(
        "# A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function",
        "# Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function",
        1,
    )
    text = text.replace(
        "> **A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta\n> Function**",
        "> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta\n> Function**",
        1,
    )
    text = text.replace("0.6730732086087052768351\\ldots", NEW_DECIMAL + r"\ldots")
    text = text.replace("0.6730732086087052768351…", NEW_DECIMAL + "…")
    text = text.replace(
        "(655000 H_MT − 1305) / 652504",
        "(1125000 H_MT − 2220) / 1120671",
    )
    text = text.replace(
        "The final local-to-global argument uses block length\n\n**m = 262.**",
        "The refined global argument preserves the exact positional pressure and uses adjacent-pair pinching with block length\n\n**m = 450.**",
    )
    text = text.replace(
        "The new ingredient is a **nonuniform position-weighted refinement** of a\nseven-point stability/local-to-global argument.",
        "The new ingredients are **exact pressure-preserving shifted-block accounting** and an **adjacent-pair pinching refinement**, built on the existing nonuniform seven-point certificate.",
    )
    text = text.replace(
        "**Current manuscript release:** `v1.1.0-paper`",
        "**Current manuscript branch:** `v17-pressure-preserving`",
    )
    text = text.replace(
        "### Manuscript\n\n**`v1.1.0-paper`**\n\nThis release freezes the submission-ready manuscript.",
        "### Previous frozen manuscript\n\n**`v1.1.0-paper`**\n\nThis release freezes the preceding submission-ready manuscript. The v17 revision is the current branch state pending its next frozen release.",
    )
    text = text.replace(
        "The submission-ready manuscript is frozen in:\n\n``` text\nv1.1.0-paper\n```",
        "The preceding submission-ready manuscript is frozen in:\n\n``` text\nv1.1.0-paper\n```\n\nThe current v17 revision is on branch `v17-pressure-preserving` pending its next frozen release.",
    )

    # Remove any old/duplicated v17 analytic-refinement appendix and append one
    # canonical block at the end.
    text = re.sub(r"\n+## v17 analytic refinement\n.*\Z", "", text, flags=re.S)
    text = text.rstrip() + f"""


## v17 analytic refinement

The v17 manuscript reuses the frozen seven-point certificate unchanged. A new
exact-arithmetic verifier in `certification/v17/verify_improved_bound.py`
checks the additional scalar kernel enclosure, pressure mass, contradiction
margin, and final constant. The v17 result is

$$
\\liminf_{{T\\to\\infty}}\\frac{{N_0^s(T,2T)}}{{N(T,2T)}}
\\ge {NEW_DECIMAL_LONG}\\ldots
$$
"""
    return text


def patch_readme() -> None:
    p = ROOT / "README.md"
    (ROOT / "README_v17.md").write_text(normalize_readme(p.read_text(encoding="utf-8")), encoding="utf-8")


def patch_citation() -> None:
    p = ROOT / "CITATION.cff"
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "Reproducibility artifact for A position-weighted refinement for simple zeros of the Riemann zeta function",
        "Reproducibility artifact for Pressure-preserving refinements for simple zeros of the Riemann zeta function",
    )
    text = re.sub(r'date-released: "[0-9-]+"', 'date-released: "2026-09-06"', text)
    text = re.sub(r'version: "[0-9.]+"', 'version: "1.2.0"', text)
    (ROOT / "CITATION_v17.cff").write_text(text, encoding="utf-8")


def patch_paper_readme() -> None:
    p = ROOT / "paper/README.md"
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "**A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function**",
        "**Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**",
    )
    text = text.replace(
        "The submission-ready manuscript is frozen in release `v1.1.0-paper`.",
        "The v17 pressure-preserving revision is maintained on branch `v17-pressure-preserving` pending its next frozen release.",
    )
    canonical = "The v17 refinement adds exact pressure-preserving averaging and adjacent-pair pinching; see `../certification/v17/` for the new exact-arithmetic verifier."
    text = re.sub(r"\n*The v17 refinement adds exact pressure-preserving averaging and adjacent-pair pinching; see `\.\./certification/v17/` for the new exact-arithmetic verifier\.\s*", "\n", text)
    text = text.rstrip() + "\n\n" + canonical + "\n"
    (ROOT / "paper/README_v17.md").write_text(text, encoding="utf-8")


if __name__ == "__main__":
    patch_main()
    patch_readme()
    patch_citation()
    patch_paper_readme()
    print("V17_PATCH_GENERATED")
