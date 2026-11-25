import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive
    (n d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e) := by
  constructor
  · rintro ⟨p, hp1, hp2⟩
    have hm1 : p ≡ n [MOD d] := hp1
    have hm2 : p ≡ 1 [MOD e] := hp2
    have h1 : p ≡ n [MOD Nat.gcd d e] := hm1.of_dvd (Nat.gcd_dvd_left d e)
    have h2 : p ≡ 1 [MOD Nat.gcd d e] := hm2.of_dvd (Nat.gcd_dvd_right d e)
    exact h1.symm.trans h2
  · intro h
    obtain ⟨k, hk1, hk2⟩ :=
      Nat.chineseRemainder' (a := n) (b := 1) (n := d) (m := e) h
    exact ⟨k, hk1, hk2⟩
