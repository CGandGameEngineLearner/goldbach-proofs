import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive :
    ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _ _
  constructor
  · rintro ⟨p, hpd, hpe⟩
    have hd : Nat.ModEq (Nat.gcd d e) p n :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_left d e) hpd
    have he : Nat.ModEq (Nat.gcd d e) p 1 :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_right d e) hpe
    exact hd.symm.trans he
  · intro h
    obtain ⟨p, hp⟩ := Nat.chineseRemainder' (n := d) (m := e) (a := n) (b := 1) h
    exact ⟨p, hp⟩
