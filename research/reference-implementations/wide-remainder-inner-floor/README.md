# `L-goldbach-wide-remainder-inner-floor`: Signed Single-Gap Reduction & Route B Reference Implementation

This directory stages the kernel-verified single-file reference implementation (`WideRemainderInnerFloor.lean`) for `L-goldbach-wide-remainder-inner-floor` while the final hypothesis `SignedMiddleRemainderFloor` (and QRH(7/8) dependency/extraction path) is being resolved.

- **Target gap**: `L-goldbach-wide-remainder-inner-floor` (final path: `lean/Conjectures/Goldbach/WideRemainderInnerFloor.lean`)
- **File size**: 10,083 lines, 462.5 KiB (< 23% of the 2 MiB single-file limit)
- **SHA256**: `dee84e39965c4a8a281fff7b65941a1c5bb8e89b9a58eb9f362453676f951393`
- **Verification**: Pinned Lean 4.36.0 + Mathlib `fc4f59e`, `LEAN_EXIT_CODE=0`, 0 `sorry`, **90 / 90** `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`.

## Replay Instructions

```bash
cd lean
lake build \
  Conjectures.Goldbach.DyadicCellShortPrimeFloor \
  Conjectures.Goldbach.ReflectionCharacterContraction \
  PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4 \
  Conjectures.Goldbach.LowSkirtFromShortProgressions \
  PEqualNP.Outside.L_goldbach_frontier_medcore_bv_band
lake env lean ../research/reference-implementations/wide-remainder-inner-floor/WideRemainderInnerFloor.lean
```

## Remaining Barrier & Closure Paths

- **Isolated Hypothesis**: `InnerFloorResearch.SignedMiddleRemainderFloor` (one-sided signed middle-band floor; completely removes the two-sided $L^2$ requirement `MiddleCellEnergySmall`).
- **Path 1 (QRH($7/8$) Direct Closure)**: Complete analytic closure yielding $O(n^{23/24}\log^{26} n) = o(n)$ using `rational_canonical_model`, `norm_window_modes`, `V1f0`, and QRH($7/8$). Blocked only on admitting a QRH($7/8$) dependency package or compressing its minimal kernel dependency cone under 2 MiB (raw `openai/math` closure is 6.89 MB / 307 modules; kernel-cone extraction is in progress).
- **Path 2 (Minimal Weak-Gap Target)**: With Jutila's log-free zero density, our verified `tripleLogGapBudget` reduces the barrier to $(1-\beta)\log n \ge 4\log\log\log n$ for $d \le n^{1/5}, |\gamma| \le (\log\log n)^{64}$.
