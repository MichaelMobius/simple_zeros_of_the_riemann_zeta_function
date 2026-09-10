from pathlib import Path
p = Path('paper/main.tex')
s = p.read_text()
old = r''' =\frac1{K(0)}\int_{-1/2}^{1/2}\cos(\sqrt2\,u)
   \left|\sum_{j=1}^m c_j e^{-2\pi i y_j u}\right|^2du\ge0,'''
new = r''' =\frac1{\sqrt2\sin(1/\sqrt2)}\int_{-1/2}^{1/2}\cos(\sqrt2\,u)
   \left|\sum_{j=1}^m c_j e^{-2\pi i y_j u}\right|^2du\ge0,'''
if s.count(old) != 1:
    raise SystemExit(f'expected one PSD normalization match, found {s.count(old)}')
p.write_text(s.replace(old, new, 1))
