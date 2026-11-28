# `buchstab-wave1` — Standalone Mathlib-Only Toolchains (`v4.36.0`)

Extracted from `Visio-Vanitas/buchstab-switching` (`on-dev`, pinned to `leanprover/lean4:v4.36.0` and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, matching `goldbach-proofs/lean/` identically) with **zero `sorry`**, **zero custom `axiom`**, and **zero `native_decide`**.

## Contents

| Package | Modules | Purpose |
| :--- | :--- | :--- |
| **`T1` Binary `Dyadic` & Taylor Bounds** | `DyadicDefs.lean`, `DyadicProofs.lean`, `ExpLogProofs.lean` | 80-bit biased binary `Dyadic` arithmetic (`<<<`/`>>>`), Q64 `artanh`/`log` witnesses, Q64 `exp`, and degree-12 rational Taylor `expPoly12` bounds |
| **`T2` `<27,000` `OddPrimeTree`** | `PrimeTable27000.lean`, `OddPrimeTreeData.lean`, `OddPrimeTree.lean` | Complete verified list of all `2,961` primes `< 27,000` + depth-6 static segment tree (`O(log N)` range queries for $\prod(1 - 1/(p-1))$ and $\sum 1/(p-1)$) |
| **`T4(k3)` Combinatorial Sieves** | `MultiplicativeOmega.lean`, `ShiftedPrimes.lean`, `OneStepSwitching.lean`, `AbstractSieve.lean`, `BonferroniHybrid.lean`, `BonferroniEstimates.lean`, `BrunBlockSieve*.lean` | Abstract Buchstab identity, Bonferroni hybrid truncation, Brun combinatorial block lower sieve (including divisor-omission monotonicity), and one-step $\Omega(m)\le 3$ switching |
| **`T7a` Arithmetic Lemmas** | `MertensTwoVar.lean`, `RobinOmega/*.lean` | Two-variable closed-interval Mertens bounds and unconditional Robin bound $\omega(N) < 1.3841 \log N / \log\log N$ ($N \ge 3$) |
| **`T8` Zero-Float Audit Tools** | `tools/interval.py`, `tools/ast_zero_float_audit.py` | `PREC = 90` outward-rounded `Decimal`/`Fraction` interval engine with global `Inexact`/`Rounded` traps, AST zero-float/zero-`math` scanner, and Lean hygiene checker |

## Reproduce

```bash
cd lean
lake exe cache get
bash ../research/reference-proofs/buchstab-wave1/verify.sh
```
