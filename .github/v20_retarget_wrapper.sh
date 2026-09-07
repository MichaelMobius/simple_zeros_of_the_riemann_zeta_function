#!/usr/bin/env bash
set -euo pipefail
python3 - <<'PY'
from pathlib import Path
p = Path('.github/v20_retarget.sh')
s = p.read_text(encoding='utf-8')
s = s.replace(
    "grep -R --include='*.yml' -nE 'part\\*\\.b64|base64 -d' .github/workflows",
    "grep -R --include='*.yml' --exclude='v20-auditability.yml' --exclude='v20-unpack-auditability.yml' -nE 'part\\*\\.b64|base64 -d' .github/workflows"
)
p.write_text(s, encoding='utf-8')
PY
bash .github/v20_retarget.sh
