#!/usr/bin/env bash
set -euo pipefail

# Canonical installer used by all Lean CI jobs.
mkdir -p scripts
cat > scripts/install_hurtado_overlay.sh <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "usage: $0 <zeta23-root>" >&2
  exit 2
fi
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TARGET="$1"
mkdir -p "$TARGET/HurtadoZeta23"
cp "$REPO_ROOT"/lean_src/HurtadoZeta23/*.lean "$TARGET/HurtadoZeta23/"
EOF
chmod +x scripts/install_hurtado_overlay.sh

python3 - <<'PY'
from pathlib import Path

wfdir = Path('.github/workflows')
for p in wfdir.glob('*.yml'):
    if p.name == 'v20-unpack-auditability.yml':
        continue
    lines = p.read_text(encoding='utf-8').splitlines(True)
    out = []
    skip_tar = False
    for line in lines:
        if skip_tar and 'tar -xzf ' in line:
            skip_tar = False
            continue
        skip_tar = False

        if 'cat harness/lean_harness/v17_adj/part*.b64' in line or 'cat harness/lean_harness/v17_analytic/part*.b64' in line:
            indent = line[:len(line) - len(line.lstrip())]
            replacement = indent + 'bash harness/scripts/install_hurtado_overlay.sh upstream/zeta23\n'
            if not out or out[-1] != replacement:
                out.append(replacement)
            skip_tar = True
            continue

        if 'cat lean_harness/v17_adj/part*.b64' in line or 'cat lean_harness/v17_analytic/part*.b64' in line:
            indent = line[:len(line) - len(line.lstrip())]
            replacement = indent + 'bash scripts/install_hurtado_overlay.sh /tmp/zeta\n'
            if not out or out[-1] != replacement:
                out.append(replacement)
            skip_tar = True
            continue

        out.append(line)

    text = ''.join(out)
    # Collapse duplicate installer invocations separated only by identical adjacent lines.
    a = '          bash harness/scripts/install_hurtado_overlay.sh upstream/zeta23\n'
    text = text.replace(a + a, a)
    b = '          bash scripts/install_hurtado_overlay.sh /tmp/zeta\n'
    text = text.replace(b + b, b)
    p.write_text(text, encoding='utf-8')

bad = []
for p in wfdir.glob('*.yml'):
    if p.name == 'v20-unpack-auditability.yml':
        continue
    text = p.read_text(encoding='utf-8')
    if '.b64' in text or 'base64 -d' in text:
        bad.append(str(p))
if bad:
    print('ENCODED_SOURCE_REFERENCES_REMAIN')
    print('\n'.join(bad))
    raise SystemExit(1)
PY

# Remove encoded transport fragments now that CI consumes ordinary .lean files.
git rm lean_harness/v17_adj/part*.b64
git rm lean_harness/v17_analytic/part*.b64

# README: make status, trust boundary, canonical source tree, and predecessor URLs explicit.
python3 - <<'PY'
from pathlib import Path
p = Path('README.md')
s = p.read_text(encoding='utf-8')

marker = 'by **Michael Hurtado**.\n'
status = '''\n> **Current default-branch manuscript:** publication-hardened v19  \
> **Mathematical theorem:** v17  \
> **Current bound:** `0.6731175265883904388095857434...`  \
> **Latest frozen theorem release:** `v1.2.0-paper`\n\n'''
if status.strip() not in s:
    if marker not in s:
        raise SystemExit('README author marker not found')
    s = s.replace(marker, marker + status, 1)

oldtree = '''├── lean_harness/\n│   ├── frozen/\n│   ├── v17_weighted/\n│   ├── v17_energy/\n│   ├── v17_strong/\n│   ├── v17_global/\n│   └── ...\n'''
newtree = '''├── lean_src/\n│   ├── HurtadoZeta23/        # canonical browseable .lean sources\n│   └── V17_FINAL_CLOSURE.txt\n├── lean_harness/             # historical/stage-specific harness files\n├── scripts/\n│   └── install_hurtado_overlay.sh\n'''
s = s.replace(oldtree, newtree)

old = '''### `lean_harness/`\n\nContains the Lean adaptation and the exact CI overlay used to compile the v17\nproof against the pinned upstream `formal-math` source tree.\n'''
new = '''### `lean_src/` and `lean_harness/`\n\n`lean_src/HurtadoZeta23/` is the canonical human-browseable Lean source tree:\nevery Hurtado module in the published v17 final closure is stored as an ordinary\n`.lean` file and can be inspected directly in GitHub.\n`lean_src/V17_FINAL_CLOSURE.txt` records the exact transitive closure of\n`HurtadoZeta23.V17FinalAssembly`. CI installs these sources on top of the pinned\nupstream `formal-math/zeta23` tree using `scripts/install_hurtado_overlay.sh`.\nThe stage-specific `lean_harness/` directories remain for provenance and CI\norganization; encoded base64/tar source fragments are no longer used.\n'''
s = s.replace(old, new, 1)

anchor = '''The exact final CI closure currently contains **127 Hurtado modules** and\nbuilds successfully against\n'''
insert = '''More explicitly, the formal stack is **Mathlib + the pinned Anthropic\n`formal-math/zeta23` formalization + the browseable `HurtadoZeta23` v17 source\ntree**, with exactly two external numerical certificate propositions at the\nfinal theorem boundary.\n\n'''
if insert.strip() not in s and anchor in s:
    s = s.replace(anchor, insert + anchor, 1)

s = s.replace(
    'The upstream work of **Sunghyeon Jo** introduced the relevant reproducible',
    'The upstream work of **[Sunghyeon Jo (`ainta`)](https://github.com/ainta/zeta-simple-zeros)** introduced the relevant reproducible'
)
s = s.replace(
    'A subsequent reproducible refinement by **Lea Rademacher** strengthened',
    'A subsequent reproducible refinement by **[Lea Rademacher](https://github.com/learademacher/ai-refines-ai-zeta-bound)** strengthened'
)

p.write_text(s, encoding='utf-8')
PY

cat > docs/V20_PUBLIC_AUDITABILITY.md <<'EOF'
# v20 public-auditability cleanup

This maintenance revision changes no mathematical statement, numerical
constant, certificate proposition, or Lean theorem. Its purpose is to make the
existing v17 formalization directly auditable in a web browser.

Changes:

- materialize the complete `HurtadoZeta23` source tree as ordinary `.lean`
  files under `lean_src/HurtadoZeta23/`;
- remove the base64-split tar fragments formerly used to transport part of the
  source tree;
- retarget Lean CI to install the canonical browseable source tree directly;
- publish `lean_src/V17_FINAL_CLOSURE.txt`, the exact transitive Hurtado import
  closure of `HurtadoZeta23.V17FinalAssembly`;
- clarify the formal stack as Mathlib + pinned Anthropic `formal-math/zeta23` +
  HurtadoZeta23, conditional on exactly two explicit external numerical
  certificate propositions;
- add direct public links to the Jo and Rademacher predecessor artifacts.

The mathematical theorem and bound are unchanged:

`0.6731175265883904388095857434...`.
EOF

# Permanent auditability check.
cat > .github/workflows/v20-auditability.yml <<'EOF'
name: V20 public Lean auditability

on:
  push:
    branches: [main, v20-public-auditability]
    paths:
      - 'lean_src/**'
      - 'lean_harness/**'
      - 'scripts/install_hurtado_overlay.sh'
      - '.github/workflows/**'
  pull_request:
    paths:
      - 'lean_src/**'
      - 'lean_harness/**'
      - 'scripts/install_hurtado_overlay.sh'
      - '.github/workflows/**'
  workflow_dispatch: {}

permissions:
  contents: read

jobs:
  auditability:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Check canonical source tree
        shell: bash
        run: |
          set -euo pipefail
          test -f lean_src/HurtadoZeta23/V17FinalAssembly.lean
          test -f lean_src/V17_FINAL_CLOSURE.txt
          grep -q '^# Modules: 127$' lean_src/V17_FINAL_CLOSURE.txt
          test "$(find lean_src/HurtadoZeta23 -maxdepth 1 -type f -name '*.lean' | wc -l)" -ge 127
          if find lean_harness -type f -name '*.b64' -print -quit | grep -q .; then
            echo 'Encoded Lean source fragments remain under lean_harness.' >&2
            exit 1
          fi
          if grep -R --include='*.yml' -nE 'part\*\.b64|base64 -d' .github/workflows; then
            echo 'A workflow still depends on encoded Lean source transport.' >&2
            exit 1
          fi
EOF

# Sanity checks before committing.
test -f lean_src/HurtadoZeta23/V17FinalAssembly.lean
grep -q '^# Modules: 127$' lean_src/V17_FINAL_CLOSURE.txt
if find lean_harness -type f -name '*.b64' -print -quit | grep -q .; then
  echo 'B64 files remain after cleanup' >&2
  exit 1
fi
if grep -R --include='*.yml' -nE 'part\*\.b64|base64 -d' .github/workflows | grep -v 'v20-unpack-auditability.yml'; then
  echo 'Legacy b64 workflow references remain' >&2
  exit 1
fi

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git add .github/workflows README.md docs/V20_PUBLIC_AUDITABILITY.md scripts lean_harness
git commit -m 'Retarget CI to browseable Lean sources'
git push origin HEAD:v20-public-auditability
