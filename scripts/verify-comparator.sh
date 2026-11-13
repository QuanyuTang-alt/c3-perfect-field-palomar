#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
command -v bwrap >/dev/null
command -v lake >/dev/null
prefix="$(lean --print-prefix)"
config="$(mktemp)"
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json, pathlib, sys
source, destination, prefix = sys.argv[1:]
config=json.loads(pathlib.Path(source).read_text())
assert 'external_kernels' not in config
config['external_kernels']={'nanoda':[f'{prefix}/bin/nanoda_bin'], 'con-ron':[f'{prefix}/bin/con-ron']}
pathlib.Path(destination).write_text(json.dumps(config))
PY
lake exe cache get
lake comparator --config "$config"
