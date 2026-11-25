import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive :
    ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _ _
  constructor
  · rintro ⟨p, hd, he⟩
    have hdn : Nat.ModEq d p n := hd
    have he1 : Nat.ModEq e p 1 := he
    exact ((hdn.of_dvd (Nat.gcd_dvd_left d e)).symm).trans
      (he1.of_dvd (Nat.gcd_dvd_right d e))
  · intro h
    exact (Nat.chineseRemainder' (show Nat.ModEq (Nat.gcd d e) n 1 from h)).exists
