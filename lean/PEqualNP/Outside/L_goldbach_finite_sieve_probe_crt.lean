import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_finite_sieve_probe_crt :
    ∀ n d e : ℕ, 0 < d → 0 < e →
      (∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔
        n % (Nat.gcd d e) = 1 % (Nat.gcd d e) := by
  intro n d e hd he
  constructor
  · rintro ⟨p, hpd, hpe⟩
    have hnd : n ≡ p [MOD d] := by
      exact hpd.symm
    have hpg : p ≡ 1 [MOD Nat.gcd d e] := by
      exact (show p ≡ 1 [MOD e] from hpe).of_dvd (Nat.gcd_dvd_right d e)
    have hng : n ≡ p [MOD Nat.gcd d e] :=
      hnd.of_dvd (Nat.gcd_dvd_left d e)
    exact hng.trans hpg
  · intro hcompat
    have hm : n ≡ 1 [MOD Nat.gcd d e] := by
      exact hcompat
    let k := Nat.chineseRemainder' hm
    exact ⟨k, k.property.1, k.property.2⟩

end PEqualNP.Outside
