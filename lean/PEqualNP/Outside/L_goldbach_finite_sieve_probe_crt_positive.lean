import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive :
    ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _ _
  constructor
  · rintro ⟨p,hd,he⟩
    have h₁ : p ≡ n [MOD d] := hd
    have h₂ : p ≡ 1 [MOD e] := he
    exact ((h₁.of_dvd (Nat.gcd_dvd_left _ _)).symm.trans
      (h₂.of_dvd (Nat.gcd_dvd_right _ _)))
  · intro h
    let c := Nat.chineseRemainder' h
    exact ⟨c, c.property.1, c.property.2⟩
