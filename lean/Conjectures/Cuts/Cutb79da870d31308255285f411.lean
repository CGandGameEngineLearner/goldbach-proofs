import Mathlib

/-!
# Cut of `L-goldbach-rough-fifth-liouville`

The frozen task asks for one constant `η ∈ (0, 2/5)` such that for every sufficiently large
even `N` the Liouville values of the complements satisfy `Σ_{p ∈ C N} λ(N - p) ≤ (2/5 - η) |C N|`,
where `C N` collects the primes `p` with `N/3 < p < 2N/3` whose complement `N - p` has no
prime factor at or below `N^(1/5)`.  The brief names the obstacle: the sum carries the
complements with three and four prime factors as well as the primes, so this is a parity
statement on the sifted support, and the Möbius-twisted distribution results in the literature
do not supply this budget.

Two independent inputs are isolated.

* `h₁` (analytic, the parity budget as a counting statement): the candidates `p ∈ C N` whose
  complement `N - p` has an odd number of prime factors, counted with multiplicity, make up at
  least a fraction `3/10 + δ` of the sifted set, for one fixed `δ ∈ (0, 1/5)`.
* `h₂` (combinatorial, sign counting): the Liouville sum over the sifted set equals the size of
  the set minus twice the number of odd-`Ω` complements.

Combination: `Σ λ = |C N| - 2 |{odd}| ≤ |C N| - 2 (3/10 + δ) |C N| = (2/5 - 2δ) |C N|`, so the
constant `η := 2δ` works.
-/

-- child 1 zh: 奇数个素因子的补数占比下界（解析输入）：存在固定的 δ∈(0,1/5)，对充分大的每个偶数 N，C N 中使 N−p 的素因子个数（计重）为奇数的 p 至少占 (3/10+δ)。
-- child 1 en: Share of odd-number-of-prime-factors complements (analytic input): for one fixed delta in (0,1/5) and every sufficiently large even N, the p in C N with N-p having an odd number of prime factors with multiplicity make up at least (3/10+delta) of C N.
-- child 2 zh: 符号计数恒等式（组合提取）：对每个 N，C N 上 λ(N−p) 之和等于 |C N| 减去奇数个素因子补数个数的两倍。
-- child 2 en: Sign-counting identity (combinatorial extraction): for every N, the sum of lambda(N-p) over C N equals the size of C N minus twice the number of members whose complement has an odd number of prime factors.

theorem Conjectures.Cuts.Cutb79da870d31308255285f411
    (h₁ : ∃ δ : ℝ, 0 < δ ∧ δ < (1 : ℝ) / 5 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ((3 : ℝ) / 10 + δ) * (((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).card : ℝ) ≤
      ((((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧
        N < (N-p).minFac^5)).filter (fun p => Odd (ArithmeticFunction.cardFactors (N-p)))).card : ℝ))
    (h₂ : ∀ N : ℕ,
      ((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧
        N < (N-p).minFac^5)).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) =
      (((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧
        N < (N-p).minFac^5)).card : ℝ) -
      2 * ((((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧
        N < (N-p).minFac^5)).filter (fun p => Odd (ArithmeticFunction.cardFactors (N-p)))).card : ℝ)) :
    (let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∃ η : ℝ, 0 < η ∧ η < 2/5 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → (C N).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) ≤ (2/5-η)*((C N).card:ℝ)) := by
  intro C
  obtain ⟨δ, hδ0, hδ1, N₀, hN₀⟩ := h₁
  refine ⟨2*δ, by positivity, by linarith, N₀, fun N hN hE => ?_⟩
  have h2 : (C N).sum (fun p => (ArithmeticFunction.liouville (N - p) : ℝ)) =
      ((C N).card : ℝ) - 2 * (((C N).filter (fun p => Odd (ArithmeticFunction.cardFactors (N - p)))).card : ℝ) :=
    h₂ N
  have h1 : ((3 : ℝ) / 10 + δ) * ((C N).card : ℝ) ≤
      (((C N).filter (fun p => Odd (ArithmeticFunction.cardFactors (N - p)))).card : ℝ) :=
    hN₀ N hN hE
  rw [h2]
  calc ((C N).card : ℝ) - 2 * (((C N).filter (fun p => Odd (ArithmeticFunction.cardFactors (N - p)))).card : ℝ)
      ≤ ((C N).card : ℝ) - 2 * (((3 : ℝ) / 10 + δ) * ((C N).card : ℝ)) := by linarith
    _ = (2/5 - 2*δ) * ((C N).card : ℝ) := by ring
