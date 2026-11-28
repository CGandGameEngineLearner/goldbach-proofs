import Mathlib

-- child 1 zh: 对每个充分大偶数 n，找到素数 p、q 及 m ≥ 13，使 n = p + q + 2m，且 m 的二进制展开至多有十三个 1。
-- child 1 en: For every sufficiently large even n, find primes p and q and m ≥ 13 with n = p + q + 2m and at most thirteen set bits in m.
-- child 2 zh: 若 m ≥ 13 且 m 的二进制展开至多有十三个 1，则 2m 可写成恰好十三个正指数二次幂之和，允许重复。
-- child 2 en: If m ≥ 13 has at most thirteen set bits, then 2m is a sum of exactly thirteen positive powers of two, allowing repetitions.

/-
The first premise concerns the support of the binary shifts. It counts no
ordered exponent tuples. For the second, start with the set bits of m and
split 2^(j+1) into two copies of 2^j. While fewer than thirteen terms
remain, their sum m ≥ 13 guarantees that some term exceeds one. Each split
adds one term and preserves the sum. Doubling the thirteen terms gives the
required positive exponents.
-/
theorem Conjectures.Cuts.Cut322cd37d5e769c41e2896d8b
    (hSupport : ∃ N : ℕ, ∀ n ≥ N, Even n → ∃ p q m : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ 13 ≤ m ∧ m.bitIndices.length ≤ 13 ∧
      n = p + q + 2 * m)
    (hExpand : ∀ m : ℕ, 13 ≤ m → m.bitIndices.length ≤ 13 →
      ∃ e : Fin 13 → ℕ, 2 * m = ∑ j, 2 ^ (e j + 1)) :
    (∃ N : ℕ, ∀ n ≥ N, Even n → ∃ (p q : ℕ) (e : Fin 13 → ℕ),
      Nat.Prime p ∧ Nat.Prime q ∧ n = p + q + ∑ j, 2 ^ (e j + 1)) := by
  obtain ⟨N, hN⟩ := hSupport
  refine ⟨N, ?_⟩
  intro n hn heven
  obtain ⟨p, q, m, hp, hq, hmin, hbits, hn'⟩ := hN n hn heven
  obtain ⟨e, he⟩ := hExpand m hmin hbits
  exact ⟨p, q, e, hp, hq, hn'.trans (congrArg (fun t : ℕ => p + q + t) he)⟩
