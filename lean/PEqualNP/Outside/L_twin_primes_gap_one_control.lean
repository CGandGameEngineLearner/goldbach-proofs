import Mathlib
theorem PEqualNP.Outside.L_twin_primes_gap_one_control : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+1) ≠ 0 → (∃ k : ℕ, n = 2^k) ∨ (∃ k : ℕ, n+1 = 2^k) := by
  intro n hn
  have hn0 : ArithmeticFunction.vonMangoldt n ≠ 0 := left_ne_zero_of_mul hn
  have hn1 : ArithmeticFunction.vonMangoldt (n+1) ≠ 0 := right_ne_zero_of_mul hn
  have hnpp : IsPrimePow n := by
    by_contra h
    apply hn0
    simp [ArithmeticFunction.vonMangoldt_apply, h]
  have hn1pp : IsPrimePow (n+1) := by
    by_contra h
    apply hn1
    simp [ArithmeticFunction.vonMangoldt_apply, h]
  have helper : ∀ m : ℕ, IsPrimePow m → 2 ∣ m → ∃ k : ℕ, m=2^k := by
    intro m hm he
    obtain ⟨p, k, hp, hk, hmk⟩ := (isPrimePow_nat_iff m).mp hm
    have hd : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (hmk ▸ he)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd |>.symm
    exact ⟨k, by simpa [hp2] using hmk.symm⟩
  rcases Nat.even_or_odd n with h | h
  · left; exact helper n hnpp ((even_iff_two_dvd).mp h)
  · right; apply helper (n+1) hn1pp
    exact (even_iff_two_dvd).mp (h.add_odd odd_one)



