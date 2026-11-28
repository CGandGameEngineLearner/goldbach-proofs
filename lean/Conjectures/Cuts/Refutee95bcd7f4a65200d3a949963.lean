import Mathlib

/-
Refutation of L-goldbach-cut-3d070a1d2c23d2914041599a.

The lemma asks: for every sufficiently large even n and every prime p with
3p <= 2n <= 6p, one of n-2, n, n+2 equals p+q with q prime.  This is false.

Construction: a = 210*m + 117 is odd, a = 3(70m+39), a-2 = 5(42m+23),
a+2 = 7(30m+17), so a-2, a, a+2 are all composite.  Take any prime p with
a < p <= 2a (Bertrand) and n = p + a.  Then n is even, n >= m,
3p <= 2n (since p <= 2a) and 2n <= 6p (since a < p), while the only
candidates q are n-p = a, n-p-2 = a-2, n-p+2 = a+2, none prime.
Hence no threshold x1 works: for every x1 there is a counterexample n >= x1.
-/

namespace Refute3d07Aux

private theorem not_prime_of {a b n : ℕ} (h : a * b = n) (ha : 1 < a) (hb : 1 < b) :
    ¬ Nat.Prime n :=
  Nat.not_prime_of_mul_eq h (by omega) (by omega)

/-- For every `m ≥ 1` there is an even `n ≥ m` and a central prime `p` such that
none of `n - p`, `n - p - 2`, `n - p + 2` is prime. -/
theorem exists_bad (m : ℕ) (hm : 1 ≤ m) :
    ∃ (n p : ℕ), m ≤ n ∧ Even n ∧ Nat.Prime p ∧ 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p ∧
      ¬ (∃ q : ℕ, Nat.Prime q ∧ p + q = n) ∧
      ¬ (∃ q : ℕ, Nat.Prime q ∧ p + q + 2 = n) ∧
      ¬ (∃ q : ℕ, Nat.Prime q ∧ p + q = n + 2) := by
  set a : ℕ := 210 * m + 117 with ha_def
  have ha3 : 3 * (70 * m + 39) = a := by omega
  have ha5 : 5 * (42 * m + 23) = a - 2 := by omega
  have ha7 : 7 * (30 * m + 17) = a + 2 := by omega
  have hna : ¬ Nat.Prime a := not_prime_of ha3 (by omega) (by omega)
  have hna2 : ¬ Nat.Prime (a - 2) := not_prime_of ha5 (by omega) (by omega)
  have hna4 : ¬ Nat.Prime (a + 2) := not_prime_of ha7 (by omega) (by omega)
  have ha_pos : a ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul a ha_pos
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hn_even : Even (p + a) := by
    refine ⟨(p + a) / 2, ?_⟩
    omega
  refine ⟨p + a, p, by omega, hn_even, hp, by omega, by omega, ?_, ?_, ?_⟩
  · rintro ⟨q, hq, heq⟩
    have hqa : q = a := by omega
    exact hna (hqa ▸ hq)
  · rintro ⟨q, hq, heq⟩
    have hqa : q = a - 2 := by omega
    exact hna2 (hqa ▸ hq)
  · rintro ⟨q, hq, heq⟩
    have hqa : q = a + 2 := by omega
    exact hna4 (hqa ▸ hq)

end Refute3d07Aux

theorem refutation :
    ¬ (∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → Even x2 → ∀ (x5 : ℕ), Nat.Prime x5 → (3 : ℕ) * x5 ≤ (2 : ℕ) * x2 → (2 : ℕ) * x2 ≤ (6 : ℕ) * x5 → (∃ (x9 : ℕ), Nat.Prime x9 ∧ x5 + x9 = x2) ∨ (∃ (x9 : ℕ), Nat.Prime x9 ∧ x5 + x9 + (2 : ℕ) = x2) ∨ ∃ (x9 : ℕ), Nat.Prime x9 ∧ x5 + x9 = x2 + (2 : ℕ)) := by
  rintro ⟨x1, h⟩
  obtain ⟨n, p, hmn, hev, hp, h1, h2, b1, b2, b3⟩ :=
    Refute3d07Aux.exists_bad (x1 + 1) (by omega)
  rcases h n (by omega) hev p hp h1 h2 with ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
  · exact b1 ⟨q, hq, heq⟩
  · exact b2 ⟨q, hq, heq⟩
  · exact b3 ⟨q, hq, heq⟩

open Refute3d07Aux in
theorem Conjectures.Cuts.Refutee95bcd7f4a65200d3a949963 : ¬ (∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → Even x2 → ∀ (x5 : ℕ), Nat.Prime x5 → (3 : ℕ) * x5 ≤ (2 : ℕ) * x2 → (2 : ℕ) * x2 ≤ (6 : ℕ) * x5 → (∃ (x9 : ℕ), Nat.Prime x9 ∧ x5 + x9 = x2) ∨ (∃ (x9 : ℕ), Nat.Prime x9 ∧ x5 + x9 + (2 : ℕ) = x2) ∨ ∃ (x9 : ℕ), Nat.Prime x9 ∧ x5 + x9 = x2 + (2 : ℕ)) := by
  first
  | exact refutation
  | exact Refute3d07Aux.exists_bad
  | exact Refute3d07Aux.not_prime_of
