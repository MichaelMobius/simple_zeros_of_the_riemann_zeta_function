from pathlib import Path

p = Path('paper/main.tex')
text = p.read_text(encoding='utf-8')

# 1. Correct the remaining technically false GitHub immutability wording.
old = '''The immutable snapshot
used for the present certificate is GitHub release
\\texttt{v1.0.0-paper}, attached to commit \\texttt{c57f53e}.'''
new = '''The frozen snapshot
used for the present certificate is GitHub release
\\texttt{v1.0.0-paper}, attached to commit \\texttt{c57f53e} and identified
additionally by the verifier and log SHA-256 values below.'''
if old not in text:
    raise SystemExit('archival snapshot wording not found')
text = text.replace(old, new, 1)

# 2. Acknowledge contemporaneous larger public claims so the literature review
# cannot be read as a numerical-record claim.
anchor = '''Rademacher's repository records Jo's artifact as its upstream provenance and
presents the subsequent refinement as AI-generated.  We cite the
human-maintained artifacts and treat model use as provenance rather than
mathematical authorship.
'''
addition = anchor + '''
Several contemporaneous public computational artifacts report numerically
larger values.  Ojha's research repository~\\cite{Ojha26} currently reports a
certified candidate bound
\\[
 0.6733127422722459\\ldots,
\\]
and explicitly labels the theorem claim a record candidate pending expert
review and end-to-end formalization.  Devine's Zenodo preprint~\\cite{Devine26}
reports the unconditional value
\\[
 0.673399.
\\]
Neither artifact is an input to the present proof.  Their proof architectures
and validation status differ from ours, so we make no claim here that the
numerical value of Theorem~\\ref{thm:main} is the largest publicly reported
bound.
'''
if anchor not in text:
    raise SystemExit('intro candidate anchor not found')
text = text.replace(anchor, addition, 1)

# 3. Add bibliography entries for those contemporaneous claims and make the
# formal-software reference directly navigable.
old_formal = '''\\bibitem{AnthropicFormal26}
Anthropic,
\\emph{formal-math: zeta23 Lean 4 formalisation},
GitHub repository \\texttt{anthropics/formal-math},
pinned by the present verification at commit
\\texttt{fbdc36bbf17d20af3fd0447c6d1a8a02773c9844} (2026).
'''
new_formal = '''\\bibitem{AnthropicFormal26}
Anthropic,
\\emph{formal-math: zeta23 Lean 4 formalisation},
GitHub repository \\texttt{anthropics/formal-math},
\\url{https://github.com/anthropics/formal-math},
pinned by the present verification at commit
\\texttt{fbdc36bbf17d20af3fd0447c6d1a8a02773c9844} (2026).

\\bibitem{Ojha26}
V.~Ojha,
\\emph{Certified lower-bound candidate for simple zeros of the Riemann zeta
function},
research repository \\texttt{trmdy/zeta-simple-zeros-673137}, 2026,
\\url{https://github.com/trmdy/zeta-simple-zeros-673137}.

\\bibitem{Devine26}
M.~Devine,
\\emph{An Unconditional 67.3399\\% Bound and Conditional Advances Beyond
67.92\\% for Simple Critical Zeros of the Riemann Zeta Function},
Zenodo, version 1.0.3, 23 August 2026,
DOI: 10.5281/zenodo.22066689.
'''
if old_formal not in text:
    raise SystemExit('formal bibliography anchor not found')
text = text.replace(old_formal, new_formal, 1)

# 4. Harden exact prose around the proof boundary.
text = text.replace(
    'The proof reuses the position-weighted seven-point certificate',
    'The proof reuses our previously certified position-weighted seven-point certificate',
    1,
)

# Safety gates.
for forbidden in [
    'The immutable snapshot',
    '\\cite{Claude26}',
    'largest publicly reported bound.\n\nSeveral',  # guard accidental duplicate insertion
]:
    if forbidden in text:
        raise SystemExit(f'stale/duplicate wording remains: {forbidden}')

for required in [
    '\\cite{Ojha26}', '\\cite{Devine26}',
    '0.6733127422722459', '0.673399',
    'no claim here that the\nnumerical value',
    'frozen snapshot',
]:
    if required not in text:
        raise SystemExit(f'required v18 audit wording missing: {required}')

p.write_text(text, encoding='utf-8')
print('final v18 adversarial-audit corrections applied')
