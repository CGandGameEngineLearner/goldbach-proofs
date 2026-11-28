import Mathlib

/-!
# Cut: split the window child by range at `10¹⁰`

Parent (`L-goldbach-cut-10d8cb571e4f3e4c6642a706`), the window obligation:

```
8·10⁹ ≤ n ≤ 10¹²  ⟹  |ψ(n;q,a) − n/φ(q)| ≤ 4√n + log n      (3 ≤ q ≤ 105, (a,q)=1)
```

The only known route is the finite computation behind BMOR (2018) Theorem 1.9 /
Appendix A.3 (`|ψ(x;q,a) − x/φ(q)| ≤ 1.745√x` up to `x₂(q) ≥ 10¹²`), i.e. a
segmented sieve plus interval arithmetic.  Its cost and certificate volume grow
with the length of the range, so we split the obligation at `10¹⁰`:

* **child 1**: `8·10⁹ ≤ n ≤ 10¹⁰`;
* **child 2**: `10¹⁰ ≤ n ≤ 10¹²`.

Each half is an independent finite computation (and, for child 1, a range of
`2·10⁹` which is within a single sieve pass).  The parent follows by `n ≤ 10¹⁰`
case analysis.
-/

-- child 1 zh: 窗口段前半：8·10⁹ ≤ n ≤ 10¹⁰ 时，误差不超过 4√n + log n（有限计算，区间约为 2×10⁹）。
-- child 1 en: First half of the window: for 8e9 <= n <= 1e10 the error is at most 4*sqrt(n) + log(n); a finite computation over a range of length 2e9.
-- child 2 zh: 窗口段后半：10¹⁰ ≤ n ≤ 10¹² 时，误差不超过 4√n + log n（有限计算，区间约为 10¹²）。
-- child 2 en: Second half of the window: for 1e10 <= n <= 1e12 the error is at most 4*sqrt(n) + log(n); a finite computation over a range of length 1e12.
theorem Conjectures.Cuts.Cutacaed69f0b396cfe9ed7b790
    (h₁ : ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      8000000000 ≤ n → n ≤ 10 ^ 10 →
        |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
          ≤ 4 * Real.sqrt (n : ℝ) + Real.log (n : ℝ))
    (h₂ : ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      10 ^ 10 ≤ n → n ≤ 10 ^ 12 →
        |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
          ≤ 4 * Real.sqrt (n : ℝ) + Real.log (n : ℝ)) :
    (∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      8000000000 ≤ n → n ≤ 10 ^ 12 →
        |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
          ≤ 4 * Real.sqrt (n : ℝ) + Real.log (n : ℝ)) := by
  intro q a n hq hq' ha hcop hn hn12
  by_cases hle : n ≤ 10 ^ 10
  · exact h₁ q a n hq hq' ha hcop hn hle
  · exact h₂ q a n hq hq' ha hcop (by omega) hn12
