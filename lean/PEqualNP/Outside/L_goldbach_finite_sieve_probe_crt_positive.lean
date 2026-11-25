import Mathlib.Data.Nat.ModEq

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive :
    ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _hd _he
  constructor
  · rintro ⟨p, hpd, hpe⟩
    have hgd : Nat.ModEq (Nat.gcd d e) p n :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_left d e) hpd
    have hge : Nat.ModEq (Nat.gcd d e) p 1 :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_right d e) hpe
    exact hgd.symm.trans hge
  · intro h
    obtain ⟨p, hpd, hpe⟩ := Nat.chineseRemainder' (n := d) (m := e) (a := n) (b := 1) h
    exact ⟨p, hpd, hpe⟩
