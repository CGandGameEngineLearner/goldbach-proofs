#!/usr/bin/env bash
set -euo pipefail
printf "Catalogue commit %s\n" "$(git rev-parse HEAD)"
python3 -B research/build_catalogue.py
python3 -B -m unittest research.test_route_sources research.test_catalogue deploy.test_landau deploy.test_publish_catalogue -v
export RUNNER_TEMP="$(mktemp -d)"
trap 'rm -rf -- "$RUNNER_TEMP"' EXIT
cd lean
curl --retry 4 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat lean-toolchain)"
time lake exe cache get
python3 - <<'PY'
import json
import os
from pathlib import Path
gaps = json.loads(Path("../research/gaps.json").read_text())["gaps"]
problems = json.loads(Path("../research/problems.json").read_text())
gaps.extend(gap for problem in problems.values() for gap in problem['gaps'])
# All current gaps are independent and can be stated using Mathlib alone.
assert all(not gap["imports"] for gap in gaps)
endpoint = next(g["statement"] for g in gaps if g["id"] == "L-goldbach-binary-pointwise-positivity")
lines = [Path("../research/strong-goldbach.lean").read_text(),
         Path("../research/check-statement-scope.lean").read_text(),
         f"example : StrongGoldbach ↔ ({endpoint}) := strongGoldbach_iff_primeMass",
         "set_option autoImplicit false"]
for gap in gaps:
    lines.extend(("", "-- " + gap["id"], "#check_statement_scope (" + gap["statement"] + ")", "example : Prop := (" + gap["statement"] + ")"))
(Path(os.environ["RUNNER_TEMP"]) / "Catalogue.lean").write_text("\n".join(lines) + "\n")
print(f"Type-checking {len(gaps)} propositions")
PY
time "$HOME/.elan/bin/lake" env lean "$RUNNER_TEMP/Catalogue.lean"
