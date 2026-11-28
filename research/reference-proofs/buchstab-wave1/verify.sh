#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$(cd "$DIR/../../../lean" && pwd)"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

export PATH="$HOME/.elan/bin:$PATH"
cd "$LEAN_DIR"

MODULES=(
  # T1 + T2: Binary Dyadic reflection, Q64 log/exp, Taylor expPoly12, <27000 OddPrimeTree
  DyadicDefs
  DyadicProofs
  ExpLogProofs
  PrimeTable27000
  OddPrimeTreeData
  OddPrimeTree
  # T4(k3): Combinatorial sieves & one-step switching
  MultiplicativeOmega
  ShiftedPrimes
  OneStepSwitching
  AbstractSieve
  BonferroniHybrid
  BonferroniEstimates
  BrunBlockSieve.SetupAndTopK
  BrunBlockSieve.ParityDecomposition
  BrunBlockSieve.MainTermAndModulus
  BrunBlockSieve.CountAndSieveBound
  BrunBlockSieve
  # T7a: Unconditional arithmetic lemmas
  MertensTwoVar
  RobinOmega.Basic
  RobinOmega.Reduction
  RobinOmega.ChebyshevLower
  RobinOmega.Asymptotic
  RobinOmega.FiniteCheck
  RobinOmega.PrimeFactorCount
)

for mod in "${MODULES[@]}"; do
  rel="${mod//./\/}.lean"
  out_rel="${mod//./\/}.olean"
  mkdir -p "$OUT/$(dirname "$out_rel")"
  echo "Compiling $rel..."
  LEAN_PATH="$OUT" lake env lean --root="$DIR" -o "$OUT/$out_rel" "$DIR/$rel"
done

python3 -I -B "$DIR/tools/ast_zero_float_audit.py" "$DIR"
echo "All ${#MODULES[@]} Lean modules and zero-float audits passed."
