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
