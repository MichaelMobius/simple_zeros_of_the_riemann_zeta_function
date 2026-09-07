from pathlib import Path

src_path = Path("scripts/apply_v18_editorial_patch_v2.py")
src = src_path.read_text(encoding="utf-8")

old = '''sub_once(
    r"The spectral trace functional \\$X\\\\mapsto\\\\operatorname\\{tr\\}\\\\Psi\\(X\\)\\$ cannot\\s+"
    r"increase under either pinching, since pinching is a random-unitary average\\s+"
    r"and this trace functional is convex and unitarily invariant\\.",
    r"""The spectral trace functional $X\\mapsto\\operatorname{tr}\\Psi(X)$ cannot
increase under either pinching by the standard pinching/majorization
principle~\\cite{Bhatia97}: pinching is a random-unitary average and this trace
functional is convex and unitarily invariant.""",
    "adjacent pinching citation",
    re.S,
)
'''

new = '''replace_once(
    "The spectral trace functional $X\\\\mapsto\\\\operatorname{tr}\\\\Psi(X)$ cannot\\n"
    "increase under either pinching, since pinching is a random-unitary average\\n"
    "and this trace functional is convex and unitarily invariant.",
    "The spectral trace functional $X\\\\mapsto\\\\operatorname{tr}\\\\Psi(X)$ cannot\\n"
    "increase under either pinching by the standard pinching/majorization\\n"
    "principle~\\\\cite{Bhatia97}: pinching is a random-unitary average and this trace\\n"
    "functional is convex and unitarily invariant.",
    "adjacent pinching citation",
)
'''

if old not in src:
    raise SystemExit("Could not locate the v2 adjacent-pinching matcher")
src = src.replace(old, new, 1)

ns = {"__name__": "__main__", "__file__": str(src_path)}
exec(compile(src, str(src_path), "exec"), ns, ns)
