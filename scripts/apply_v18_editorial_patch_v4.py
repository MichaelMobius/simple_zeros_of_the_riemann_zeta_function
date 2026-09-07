from pathlib import Path

src_path = Path("scripts/apply_v18_editorial_patch_v2.py")
src = src_path.read_text(encoding="utf-8")
start = src.index('sub_once(\n    r"The spectral trace functional')
end = src.index('\n\nreplace_once(\n    "The complete 256-bit', start)
replacement = '''replace_once(
    "The spectral trace functional \\\\(X\\\\mapsto\\\\operatorname{tr}\\\\Psi(X)\\\\) cannot\\n"
    "increase under either pinching, since pinching is a random-unitary average\\n"
    "and this trace functional is convex and unitarily invariant.",
    "The spectral trace functional \\\\(X\\\\mapsto\\\\operatorname{tr}\\\\Psi(X)\\\\) cannot\\n"
    "increase under either pinching by the standard pinching/majorization\\n"
    "principle~\\\\cite{Bhatia97}: pinching is a random-unitary average and this trace\\n"
    "functional is convex and unitarily invariant.",
    "adjacent pinching citation",
)'''
src = src[:start] + replacement + src[end:]
ns = {"__name__": "__main__", "__file__": str(src_path)}
exec(compile(src, str(src_path), "exec"), ns, ns)
