#!/usr/bin/env python3
from pathlib import Path
import hashlib, re, sys

ROOT = Path(__file__).resolve().parents[2]
FRAG = Path(__file__).resolve().parent
EXPECTED = "6bbaf51eeab527ec5f1c35bd4bdb1bb2cfb6476e"

def git_blob_sha1(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def repl(text, pattern, replacement, label, flags=re.S):
    out,n=re.subn(pattern, lambda m: replacement, text, count=1, flags=flags)
    if n != 1:
        raise RuntimeError(f"{label}: expected 1 replacement, got {n}")
    return out

def frag(name):
    return (FRAG/name).read_text(encoding="utf-8").rstrip()

def patch_main():
    src=ROOT/"paper/main.tex"
    data=src.read_bytes()
    got=git_blob_sha1(data)
    if got != EXPECTED:
        raise RuntimeError(f"paper/main.tex blob mismatch: expected {EXPECTED}, got {got}")
    t=data.decode()
    t=repl(t,r"% Manuscript version v16:[^\n]*",
           "% Manuscript version v17: pressure-preserving averaging and adjacent-pair refinement.",
           "version",flags=0)
    t=repl(t,r"\\title\{[^{}]*\}",
           r"\title{Pressure-preserving refinements for simple zeros of the Riemann zeta function}",
           "title",flags=0)
    t=repl(t,r"\\date\{[^{}]*\}",r"\date{September 6, 2026}","date",flags=0)
    t=repl(t,r"\\begin\{abstract\}.*?\\end\{abstract\}",frag("abstract.tex"),"abstract")
    t=repl(t,
      r"The contribution of the present paper is narrower and explicit\..*?"
      r"After global redistribution and shifted-block averaging, the block length\s*"
      r"\\\(m=262\\\) yields the theorem below\.",
      frag("intro.tex"),"intro")
    t=repl(t,r"\\begin\{theorem\}\[Main theorem\]\\label\{thm:main\}.*?\\end\{theorem\}",
           frag("theorem.tex"),"theorem")
    t=repl(t,
      r"\\paragraph\{Priority convention\.\}.*?(?=\\section\{The common finite compression)",
      frag("priority.tex")+"\n\n","priority")
    t=repl(t,
      r"\\begin\{proposition\}\[Pressure redistribution\]\\label\{prop:redist\}.*?\\end\{proof\}",
      frag("redist.tex"),"redistribution")
    t=repl(t,
      r"\\begin\{corollary\}\\label\{cor:energy\}.*?(?=\\section\{Comparison and structural interpretation\})",
      frag("core.tex")+"\n\n","block core")
    t=repl(t,
      r"\\section\{Comparison and structural interpretation\}.*?(?=\\section\{Scope and trust base\})",
      frag("comparison.tex")+"\n\n","comparison")
    anchor=("Proposition~\\ref{prop:cert} is computer-assisted.  Its trust base includes the")
    i=t.find(anchor)
    if i<0: raise RuntimeError("trust anchor not found")
    j=t.find("\n\n",i)
    if j<0: raise RuntimeError("trust paragraph end not found")
    t=t[:j+2]+frag("trust.tex")+"\n\n"+t[j+2:]
    t=repl(t,r"\\section\{Exact arithmetic\}.*?(?=\\begin\{thebibliography\})",
           frag("exact.tex")+"\n\n","exact arithmetic")
    out=ROOT/"paper/main_v17.tex"
    out.write_text(t,encoding="utf-8")
    print("main_v17_sha256",hashlib.sha256(t.encode()).hexdigest())

def patch_readme():
    p=ROOT/"README.md"; t=p.read_text()
    t=t.replace("# A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function",
                "# Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function",1)
    t=t.replace("> **A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta\n> Function**",
                "> **Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta\n> Function**",1)
    t=t.replace("0.6730732086087052768351\\ldots","0.6731175265883904388096\\ldots")
    t=t.replace("0.6730732086087052768351…","0.6731175265883904388096…")
    t=t.replace("(655000 H_MT − 1305) / 652504",
                "(1125000 H_MT − 2220) / 1120671")
    t=t.replace("The final local-to-global argument uses block length\n\n**m = 262.**",
                "The refined global argument preserves the exact positional pressure and uses adjacent-pair pinching with block length\n\n**m = 450.**")
    t=t.replace("The new ingredient is a **nonuniform position-weighted refinement** of a\nseven-point stability/local-to-global argument.",
                "The new ingredients are **exact pressure-preserving shifted-block accounting** and an **adjacent-pair pinching refinement**, built on the existing nonuniform seven-point certificate.")
    t=t.replace("**Current manuscript release:** `v1.1.0-paper`",
                "**Current manuscript branch:** `v17-pressure-preserving`")
    t += "\n\n## v17 analytic refinement\n\nThe v17 manuscript reuses the frozen seven-point certificate unchanged.  A new exact-arithmetic verifier in `certification/v17/verify_improved_bound.py` checks the additional scalar kernel enclosure, pressure mass, contradiction margin, and final constant.  The v17 result is\n\n$$\n\\liminf_{T\\to\\infty}\\frac{N_0^s(T,2T)}{N(T,2T)}\\ge 0.6731175265883904388095857434\\ldots\n$$\n"
    (ROOT/"README_v17.md").write_text(t)

def patch_citation():
    p=ROOT/"CITATION.cff"; t=p.read_text()
    t=t.replace("Reproducibility artifact for A position-weighted refinement for simple zeros of the Riemann zeta function",
                "Reproducibility artifact for Pressure-preserving refinements for simple zeros of the Riemann zeta function")
    t=t.replace('date-released: "2026-08-13"','date-released: "2026-09-06"')
    t=t.replace('version: "1.1.0"','version: "1.2.0"')
    (ROOT/"CITATION_v17.cff").write_text(t)

def patch_paper_readme():
    p=ROOT/"paper/README.md"; t=p.read_text()
    t=t.replace("**A Position-Weighted Refinement for Simple Zeros of the Riemann Zeta Function**",
                "**Pressure-Preserving Refinements for Simple Zeros of the Riemann Zeta Function**")
    t=t.replace("The submission-ready manuscript is frozen in release `v1.1.0-paper`.",
                "The v17 pressure-preserving revision is maintained on branch `v17-pressure-preserving` pending its next frozen release.")
    t += "\nThe v17 refinement adds exact pressure-preserving averaging and adjacent-pair pinching; see `../certification/v17/` for the new exact-arithmetic verifier.\n"
    (ROOT/"paper/README_v17.md").write_text(t)

if __name__=="__main__":
    patch_main(); patch_readme(); patch_citation(); patch_paper_readme()
    print("V17_PATCH_GENERATED")
