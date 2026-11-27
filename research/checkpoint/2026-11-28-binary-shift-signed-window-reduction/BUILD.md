# Reproducing the Lean checks

Start in this checkpoint directory. The project uses Lean 4.36.0 and mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

```sh
checkpoint="$PWD"
cd "$(git rev-parse --show-toplevel)/lean"
lake exe cache get
lake env python3 "$checkpoint/rebuild.py" StrippedResidualTerminal
```

This rebuilds the 19 research modules in the main implication and their upstream imports. Omit `StrippedResidualTerminal` to check all six endpoints in `sources.json`. Each Lean process uses one thread. The script writes its intermediate sources and object files to a temporary directory. The final `#print axioms` commands print the axiom lists for the terminal declarations.

Run `python3 "$checkpoint/rebuild.py" --sources-only` from the same `lean/` directory to check the source hashes and the import graph without compiling.

## Upstream sources

The checked upstream snapshot is [1fe24b28926cd452b7a35f71ae1fc1cb82e01e84](https://github.com/CGandGameEngineLearner/goldbach-proofs/tree/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84). The original lease used [0b4bd06b3b9bf3c35c8bb52f961744e31552e3f2](https://github.com/CGandGameEngineLearner/goldbach-proofs/tree/0b4bd06b3b9bf3c35c8bb52f961744e31552e3f2). The source of `ShortProgressionsMeanTheta` used in the main reduction is present in the checked snapshot. The script accepts current upstream files with matching SHA-256 digests. For other revisions it reads the recorded snapshot from the local Git object database. A shallow checkout with differing files needs the snapshot available locally.

Two upstream files share helper names with the exceptional-zero criterion. The replay constructs the exact two compatibility modules recorded in `sources.json` and checks the hashes of the generated Lean sources before invoking Lean.

- `ShiftSignedCommonLowBase` applies the prefix `BinaryShiftLocal` to the two overlapping namespaces in [LowSkirtFromShortProgressions.lean](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84/lean/Conjectures/Goldbach/LowSkirtFromShortProgressions.lean).
- `DeepCompatibleNoSiegel` uses three estimates with the same declarations in the accepted [DeepThreeQuartersExceptionalZeroCriterion](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84/lean/Conjectures/Goldbach/DeepThreeQuartersExceptionalZeroCriterion.lean). It retains the upstream no-Siegel-zero argument from line 983 onward in [L_goldbach_frontier_no_siegel_zero.lean](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84/lean/PEqualNP/Outside/L_goldbach_frontier_no_siegel_zero.lean). `ConductorIncidenceTerminal` uses the original no-Siegel-zero module through a separate import graph.
- `B13GaussProjection` contains the Gauss-sum estimates used to bound the linear and quadratic terms. It keeps the declaration names and attribution from the [B13 proof](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/0b4bd06b3b9bf3c35c8bb52f961744e31552e3f2/lean/Conjectures/Goldbach/B13NondividingResidueReduction.lean). The imported source chunks are lines 3–13, 2435–2439, 2895–2906, 3616–3910 and 4224–4258 at Git blob `62f8605e62540f2d0e1a8a81b15fe5bd4e747e1c`.
