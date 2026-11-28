#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../../../../.." && pwd)
cd "$repo_root/lean"

module=Conjectures.Goldbach.FinitePostBoundaryThrough262144
module_path=Conjectures/Goldbach/FinitePostBoundaryThrough262144
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT

mkdir -p "$scratch/Conjectures/Goldbach"
cp ../research/reference-proofs/FinitePostBoundaryThrough262144.lean "$scratch/$module_path.lean"
cat > "$scratch/statement.txt" <<'LEAN'
∀ j : ℕ, 16385 ≤ j → j ≤ 131072 → let n : ℕ := 4000000000000000000 + 2*j; ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n
LEAN

lake build checklemma PEqualNP.Defs
lake env lean --root="$scratch" -o "$scratch/$module_path.olean" "$scratch/$module_path.lean"
lake env sh -c '
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  exec .lake/build/bin/checklemma "$2" "$1/statement.txt" check
' check-post-boundary "$scratch" "$module"
