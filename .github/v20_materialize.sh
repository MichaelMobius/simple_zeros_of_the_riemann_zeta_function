#!/usr/bin/env bash
set -euo pipefail

if [ -f lean_src/HurtadoZeta23/V17FinalAssembly.lean ]; then
  echo 'Lean sources already materialized.'
  exit 0
fi

rm -rf /tmp/hurtado-v20
mkdir -p /tmp/hurtado-v20

cat lean_harness/v17_adj/part*.b64 | base64 -d > /tmp/hurtado-v20/core.tar.gz
tar -xzf /tmp/hurtado-v20/core.tar.gz -C /tmp/hurtado-v20
cat lean_harness/v17_analytic/part*.b64 | base64 -d > /tmp/hurtado-v20/analytic.tar.gz
tar -xzf /tmp/hurtado-v20/analytic.tar.gz -C /tmp/hurtado-v20

test -d /tmp/hurtado-v20/HurtadoZeta23
mkdir -p lean_src/HurtadoZeta23
cp /tmp/hurtado-v20/HurtadoZeta23/*.lean lean_src/HurtadoZeta23/

for d in frozen v17_scalar v17_weighted v17_adj v17_matching v17_threshold v17_energy v17_strong v17_concrete v17_endgame v17_global; do
  if compgen -G "lean_harness/$d/*.lean" > /dev/null; then
    cp lean_harness/$d/*.lean lean_src/HurtadoZeta23/
  fi
done

test -f lean_src/HurtadoZeta23/V17FinalAssembly.lean

python3 - <<'PY'
from pathlib import Path
root = Path('lean_src')
todo = ['HurtadoZeta23.V17FinalAssembly']
seen = set()
missing = []
while todo:
    mod = todo.pop()
    if mod in seen:
        continue
    seen.add(mod)
    path = root / (mod.replace('.', '/') + '.lean')
    if not path.exists():
        missing.append((mod, '<root>'))
        continue
    for line in path.read_text(encoding='utf-8').splitlines():
        s = line.strip()
        if not s.startswith('import '):
            continue
        for dep in s[len('import '):].split():
            if dep.startswith('HurtadoZeta23.'):
                dpath = root / (dep.replace('.', '/') + '.lean')
                if dpath.exists():
                    todo.append(dep)
                else:
                    missing.append((dep, mod))
if missing:
    for dep, parent in missing:
        print('MISSING', parent, '->', dep)
    raise SystemExit(1)
mods = sorted(seen)
Path('lean_src/V17_FINAL_CLOSURE.txt').write_text(
    '# Exact Hurtado v17 final import closure\n'
    '# Root: HurtadoZeta23.V17FinalAssembly\n'
    f'# Modules: {len(mods)}\n\n' + '\n'.join(mods) + '\n',
    encoding='utf-8')
print('FINAL_CLOSURE_MODULES', len(mods))
PY

cat > lean_src/README.md <<'EOF'
# Canonical browseable Lean sources

This directory contains the canonical human-browseable source tree for the
Hurtado v17 formalization. Every `HurtadoZeta23` module used by the published
final closure is stored here as an ordinary `.lean` file.

`V17_FINAL_CLOSURE.txt` lists the exact transitive `HurtadoZeta23` import
closure of `HurtadoZeta23.V17FinalAssembly`.
EOF

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add lean_src
git commit -m 'Materialize browseable Hurtado Lean sources'
git push origin HEAD:v20-public-auditability
