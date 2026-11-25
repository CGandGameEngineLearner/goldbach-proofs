import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt (n d e : ℕ) (_hd : 0 < d)
    (_he : 0 < e) :
    (∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔
      n % (Nat.gcd d e) = 1 % (Nat.gcd d e) := by
  constructor
  · rintro ⟨p, hp1, hp2⟩
    have hgd : Nat.gcd d e ∣ d := Nat.gcd_dvd_left d e
    have hge : Nat.gcd d e ∣ e := Nat.gcd_dvd_right d e
    have h1 : p % Nat.gcd d e = n % Nat.gcd d e := by
      rw [← Nat.mod_mod_of_dvd p hgd, hp1, Nat.mod_mod_of_dvd n hgd]
    have h2 : p % Nat.gcd d e = 1 % Nat.gcd d e := by
      rw [← Nat.mod_mod_of_dvd p hge, hp2, Nat.mod_mod_of_dvd 1 hge]
    rw [← h1, h2]
  · intro h
    obtain ⟨k, hk1, hk2⟩ :=
      Nat.chineseRemainder' (n := d) (m := e) (a := n) (b := 1) h
    exact ⟨k, hk1, hk2⟩
