# GRH proof source

This directory contains the Lean source and attribution files from
[lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact).
Lean module paths are prefixed with `PEqualNP.GRHSource` so the platform checker
replays their declarations in the kernel.
The platform builds the proof against its pinned Lean and Mathlib versions.

List `PEqualNP.GRH` in a task's `imports` to allow proofs for that task to
import the five theorems.

- `riemannHypothesis`
- `riemannZeta_eq_zero_re`
- `LFunction_ne_zero_of_half_lt_re`
- `LFunction_eq_zero_re`
- `LFunction_eq_zero_re_of_isPrimitive`
