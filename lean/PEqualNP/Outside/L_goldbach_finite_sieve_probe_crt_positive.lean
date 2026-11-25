import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive : ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _ _
  change (∃ p : ℕ, p ≡ n [MOD d] ∧ p ≡ 1 [MOD e]) ↔ n ≡ 1 [MOD d.gcd e]
  constructor
  · rintro ⟨p, hd, he⟩
    exact (hd.of_dvd (Nat.gcd_dvd_left d e)).symm.trans (he.of_dvd (Nat.gcd_dvd_right d e))
  · intro h
    exact ⟨(Nat.chineseRemainder' h).val, (Nat.chineseRemainder' h).property⟩
