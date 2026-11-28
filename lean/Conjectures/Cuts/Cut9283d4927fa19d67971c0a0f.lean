import Mathlib

/-!
# Cut of `L-goldbach-binary-shift-shared-exponent`

The frozen task asks for one exponent `e ≥ 2` with `2 ^ (2e) ≤ n` such that both
adjacent even targets `n - 2^e` and `n + 2 - 2^e` are sums of two primes.

Two independent inputs are isolated.

* `h₁` (analytic): for every sufficiently large even `n`, the number of admissible
  shifts that work for `n - 2^e` plus the number that work for `n + 2 - 2^e` exceeds the
  total number of admissible shifts.  This is an averaged statement over the `O(log n)`
  shifts of each single target.
* `h₂` (combinatorial pigeonhole): two shift families inside the admissible shift set
  whose sizes add up to more than the whole set share a common shift, which is then a
  witness for the frozen statement.

The bridge is the pigeonhole principle on the finite set of admissible shifts.
-/

-- child 1 zh: 相邻目标的好移位密度（解析输入）：对每个充分大的偶数 n，使 n − 2^e 为两素数之和的可容许移位数加上使 n + 2 − 2^e 为两素数之和的可容许移位数，严格大于可容许移位总数。
-- child 1 en: Good-shift density for adjacent targets (analytic input): for every sufficiently large even n, the number of admissible shifts e with n - 2^e a sum of two primes plus the number with n + 2 - 2^e a sum of two primes exceeds the total number of admissible shifts e (2 ≤ e, 2^(2e) ≤ n).
-- child 2 zh: 鸽巢提取：若两个好移位族的大小之和超过可容许移位集的总数，则它们有公共移位 e，该 e 同时是 n − 2^e 与 n + 2 − 2^e 的见证。
-- child 2 en: Pigeonhole extraction: if the sizes of the two good-shift families add up to more than the total number of admissible shifts, they share a common shift e, which witnesses the frozen statement for both n - 2^e and n + 2 - 2^e.

theorem Conjectures.Cuts.Cut9283d4927fa19d67971c0a0f
    (h₁ : ∃ N : ℕ, ∀ n ≥ N, Even n →
      ({e ∈ Finset.Icc 1 n | 2 ≤ e ∧ (2^e)^2 ≤ n ∧
        0 < ((Finset.range (n - 2^e + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n - 2^e - p))).card}).card +
      ({e ∈ Finset.Icc 1 n | 2 ≤ e ∧ (2^e)^2 ≤ n ∧
        0 < ((Finset.range (n + 2 - 2^e + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n + 2 - 2^e - p))).card}).card >
      ({e ∈ Finset.Icc 1 n | 2 ≤ e ∧ (2^e)^2 ≤ n}).card)
    (h₂ : ∀ n : ℕ,
      ({e ∈ Finset.Icc 1 n | 2 ≤ e ∧ (2^e)^2 ≤ n ∧
        0 < ((Finset.range (n - 2^e + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n - 2^e - p))).card}).card +
      ({e ∈ Finset.Icc 1 n | 2 ≤ e ∧ (2^e)^2 ≤ n ∧
        0 < ((Finset.range (n + 2 - 2^e + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n + 2 - 2^e - p))).card}).card >
      ({e ∈ Finset.Icc 1 n | 2 ≤ e ∧ (2^e)^2 ≤ n}).card →
      ∃ e : ℕ, 2 ≤ e ∧ (2^e)^2 ≤ n ∧
        0 < ((Finset.range (n - 2^e + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n - 2^e - p))).card ∧
        0 < ((Finset.range (n + 2 - 2^e + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n + 2 - 2^e - p))).card) :
    (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card;
      ∃ N : ℕ, ∀ n ≥ N, Even n → ∃ e : ℕ, 2 ≤ e ∧ (2^e)^2 ≤ n ∧ 0 < G (n-2^e) ∧ 0 < G (n+2-2^e)) := by
  obtain ⟨N, hN⟩ := h₁
  refine ⟨N, fun n hn he => ?_⟩
  obtain ⟨e, he2, he4, hgA, hgB⟩ := h₂ n (hN n hn he)
  exact ⟨e, he2, he4, hgA, hgB⟩
