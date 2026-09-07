from pathlib import Path

src_path = Path("scripts/apply_v18_editorial_patch_v4.py")
# v4 is a wrapper around v2, so instead patch v2 directly as source and include
# both known matcher repairs.
base = Path("scripts/apply_v18_editorial_patch_v2.py").read_text(encoding="utf-8")

# Repair adjacent-pair inline-math matcher by replacing the whole matcher block.
start = base.index('sub_once(\n    r"The spectral trace functional')
end = base.index('\n\nreplace_once(\n    "The complete 256-bit', start)
adj = '''replace_once(
    "The spectral trace functional \\\\(X\\\\mapsto\\\\operatorname{tr}\\\\Psi(X)\\\\) cannot\\n"
    "increase under either pinching, since pinching is a random-unitary average\\n"
    "and this trace functional is convex and unitarily invariant.",
    "The spectral trace functional \\\\(X\\\\mapsto\\\\operatorname{tr}\\\\Psi(X)\\\\) cannot\\n"
    "increase under either pinching by the standard pinching/majorization\\n"
    "principle~\\\\cite{Bhatia97}: pinching is a random-unitary average and this trace\\n"
    "functional is convex and unitarily invariant.",
    "adjacent pinching citation",
)'''
base = base[:start] + adj + base[end:]

# Make the archival snapshot wording robust to line wrapping.  We retain the
# stronger cryptographic wording elsewhere and only need to remove the false
# implication of GitHub-enforced immutability here.
needle = '''replace_once(\n    "The immutable snapshot used for the present certificate is GitHub release'''
start = base.index(needle)
end = base.index('\n\nreplace_once(\n    "\\\\section{Comparison and structural interpretation}', start)
arch = '''text = text.replace(
    "The immutable snapshot used for the present certificate is GitHub release",
    "The frozen snapshot used for the present certificate is GitHub release",
    1,
)'''
base = base[:start] + arch + base[end:]

ns = {"__name__": "__main__", "__file__": str(src_path)}
exec(compile(base, str(src_path), "exec"), ns, ns)
