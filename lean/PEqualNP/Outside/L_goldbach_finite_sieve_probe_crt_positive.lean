import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive :
    ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _hd _he
  constructor
  · rintro ⟨p, hp_d, hp_e⟩
    -- Reduce both congruences to the common modulus `gcd d e`.
    have hpd : p ≡ n [MOD Nat.gcd d e] :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_left d e) hp_d
    have hpe : p ≡ 1 [MOD Nat.gcd d e] :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_right d e) hp_e
    exact hpd.symm.trans hpe
  · intro h
    -- `h` is precisely the compatibility hypothesis of the generalized CRT.
    obtain ⟨k, hk_d, hk_e⟩ :=
      Nat.chineseRemainder' (n := d) (m := e) (a := n) (b := 1) h
    exact ⟨k, hk_d, hk_e⟩
