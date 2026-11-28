# Proposal: use the existing Bhowmik–Grimmelt formalization for `L-goldbach-grh-goldbach-exception-density`

Status: infrastructure proposal, not a proof submission.

## The frozen gap

`L-goldbach-grh-goldbach-exception-density` asks, under GRH for every Dirichlet
`L`-function, for every `ε > 0`,

```text
E(X) ≤ C * X^(1/2 + ε)     eventually,
```

where `E(X)` counts even `n` with `4 ≤ n ≤ X` that are not a sum of two primes.

## An existing complete formalization

`sthubbar/goldbach-lean`, entry `entries/bhowmikgrimmelt2026`, proves Theorem 3.1
of Bhowmik–Grimmelt, *The exceptional set of the Goldbach problem*,
arXiv:2607.27282v2, page 9:

```lean
theorem LeanLab.BhowmikGrimmelt2026.theorem31_ported1122 :
    ∀ Θ, Θ < 3 / 4 → ZeroBound Θ →
      ∀ ε > 0, PowerBound (2 * Θ - 1 / 2 + ε)
```

with

```lean
def ZeroBound (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re ≤ Θ
```

and `PowerBound θ` meaning `E(X) ≤ C * X^θ` for every `X ≥ 1`.

At `Θ = 1/2`, this gives `PowerBound ε`, which is stronger than the frozen
`X^(1/2+ε)` target. The target's GRH hypothesis (`s.re = 1/2`) implies
`ZeroBound (1/2)`, and the two definitions of `E` agree (the target's inner
filter is `¬ IsGoldbachSum n`; `Even n` is `n % 2 = 0`).

The entry reports:

- `sorry_count: 0`, `axioms: []`;
- the theorem's axioms are `propext`, `Classical.choice`, `Quot.sound`;
- 349 modules in the import closure (108 used by the theorem);
- pinned to Lean/Mathlib `v4.35.0-rc3`;
- license Apache-2.0, with attribution in its `PORTING.md`.

Links:

- <https://github.com/sthubbar/goldbach-lean/tree/main/entries/bhowmikgrimmelt2026>
- <https://github.com/sthubbar/goldbach-lean/blob/main/entries/bhowmikgrimmelt2026/LeanLab/BhowmikGrimmelt2026/Theorem31Ported1122.lean>
- <https://github.com/sthubbar/goldbach-lean/blob/main/entries/bhowmikgrimmelt2026/formalization.yaml>

## Why it cannot be submitted directly

The authoritative checker accepts exactly one added file:

```text
lean/PEqualNP/Outside/L_<gap>.lean
```

of at most 512 KiB, importing only `Mathlib` / `Mathlib.*` and the modules listed
in the gap's `imports` field (currently empty). The external proof is a
multi-megabyte, 349-module library pinned to `v4.35.0-rc3`; it cannot be imported
or concatenated into one 512 KiB file, and it would need a port to `v4.36.0`.

## Requested integration options

1. **Maintainer-managed dependency (preferred).**
   Add the external library, or a vetted subset, to the base repository's Lake
   setup; add a small bridge module that derives the frozen statement from
   `theorem31_ported1122` and the target definitions; add that bridge module to
   the gap's `imports`. Then the one-file proof can simply import the bridge.

2. **Vendored outside modules.**
   Vendor the needed modules under `PEqualNP.Outside.*`, port them to the pinned
   toolchain, make each pass `outside-guard`, and list them in the gap's
   `imports`. This is a large multi-PR project and may exceed the checker's
   150-minute build budget.

3. **Independent short proof.**
   Formalize the explicit formula and circle method from scratch in one 512 KiB
   file. This is not realistic without a substantial library.

This document is a request for a maintainer decision on option 1 or 2. No proof
is claimed here, and no frozen statement is changed.
