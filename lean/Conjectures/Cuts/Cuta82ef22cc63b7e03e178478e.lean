import Mathlib

/-!
# Cut of `L-goldbach-rough-fifth-triples`

The frozen task asks that, for every sufficiently large even `N`, at most three tenths of the
central rough candidates `C N` have a complement `N - p` with exactly three prime factors
(counted with multiplicity).

Write `T₃`, `G`, `L` for, respectively, the number of `Ω = 3` complements, the number of prime
complements (Goldbach representations inside `C N`), and the Liouville sum
`Σ_{p ∈ C N} λ(N - p)`.  Because the fifth-power roughness condition forces
`1 ≤ Ω(N - p) ≤ 4` and `λ = (-1)^Ω`, the elementary parity identity

    2 G = |C N| - L - 2 T₃

holds; it is an unconditional finite combinatorial fact, independent of any analytic input.
Solving for the target bound gives

    10 T₃ = 5 (|C N| - L - 2 G) ≤ 3 |C N|   ⟺   2 |C N| ≤ 5 L + 10 G.

The cut isolates two independent inputs:

* `h₁` (analytic, the parity budget): a lower bound on the Liouville sum together with the
  Goldbach representation count, `2 |C N| ≤ 5 L + 10 G`, for all sufficiently large even `N`.
  This is where the parity / level barrier sits: it is a correlation statement between the
  Liouville function and the primes, not a one-dimensional upper-bound sieve estimate.
* `h₂` (combinatorial, sign counting): the finite identity `2 G = |C N| - L - 2 T₃` for every
  `N`.  It follows from `1 ≤ Ω ≤ 4` on the sifted support, hence can be proved in Mathlib alone.

Combination is pure linear arithmetic: from `h₂` one gets `10 T₃ = 5(|C N| - L - 2G)`, and
`h₁` turns the right-hand side into at most `3 |C N|`.
-/

-- child 1 zh: 解析 parity 预算（Liouville 和与哥德巴赫表示数的联合下界）：存在 N₀，对每个充分大的偶数 N，中央粗糙候选集满足 2|C N| ≤ 5·Σ_{p∈C N} λ(N−p) + 10·#{p∈C N : N−p 为素数}。
-- child 1 en: Analytic parity budget (joint lower bound on the Liouville sum and Goldbach count): for some N0 and every sufficiently large even N, 2|C N| <= 5*sum_{p in C N} lambda(N-p) + 10*#{p in C N : N-p prime}, where C N is the central fifth-rough candidate set.
-- child 2 zh: 符号计数恒等式（组合提取，无条件）：对每个 N，2·#{p∈C N : N−p 为素数} = |C N| − Σ_{p∈C N} λ(N−p) − 2·#{p∈C N : Ω(N−p)=3}。
-- child 2 en: Unconditional sign-counting identity: for every N, 2*#{p in C N : N-p prime} = |C N| - sum_{p in C N} lambda(N-p) - 2*#{p in C N : Omega(N-p)=3}.

theorem Conjectures.Cuts.Cuta82ef22cc63b7e03e178478e
    (h₁ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      2 * (((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).card : ℝ) ≤
      5 * ((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ))
      + 10 * ((((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).filter (fun p => Nat.Prime (N-p))).card : ℝ))
    (h₂ : ∀ N : ℕ,
      2 * ((((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).filter (fun p => Nat.Prime (N-p))).card : ℝ) =
      (((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).card : ℝ)
      - ((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ))
      - 2 * ((((Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
        1 < N-p ∧ N < (N-p).minFac^5)).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card : ℝ)) :
    (let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
      1 < N-p ∧ N < (N-p).minFac^5);
     ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
       10*((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card ≤ 3*(C N).card) := by
  intro C
  obtain ⟨N₀, hN₀⟩ := h₁
  refine ⟨N₀, fun N hN hE => ?_⟩
  have h1 : 2 * ((C N).card : ℝ) ≤
      5 * (C N).sum (fun p => (ArithmeticFunction.liouville (N - p) : ℝ))
      + 10 * (((C N).filter (fun p => Nat.Prime (N - p))).card : ℝ) := by
    simpa [C] using hN₀ N hN hE
  have h2 : 2 * (((C N).filter (fun p => Nat.Prime (N - p))).card : ℝ) =
      ((C N).card : ℝ) - (C N).sum (fun p => (ArithmeticFunction.liouville (N - p) : ℝ))
      - 2 * (((C N).filter (fun p => ArithmeticFunction.cardFactors (N - p) = 3)).card : ℝ) := by
    simpa [C] using h₂ N
  have hreal :
      (10 : ℝ) * (((C N).filter (fun p => ArithmeticFunction.cardFactors (N - p) = 3)).card : ℝ)
        ≤ 3 * ((C N).card : ℝ) := by
    nlinarith [h1, h2]
  exact_mod_cast hreal
