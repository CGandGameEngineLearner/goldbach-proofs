import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.ModEq

/-- A pair of congruences `p ≡ n [MOD d]`, `p ≡ 1 [MOD e]` is solvable in `p` exactly when
the two residues already agree modulo `Nat.gcd d e`. -/
theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt :
    ∀ n d e : ℕ, 0 < d → 0 < e →
      ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔
        n % Nat.gcd d e = 1 % Nat.gcd d e) := by
  intro n d e _hd _he
  constructor
  · rintro ⟨p, hp1, hp2⟩
    have h1 : p ≡ n [MOD d] := hp1
    have h2 : p ≡ 1 [MOD e] := hp2
    have hgd : Nat.gcd d e ∣ d := Nat.gcd_dvd_left d e
    have hge : Nat.gcd d e ∣ e := Nat.gcd_dvd_right d e
    have h1' : p ≡ n [MOD Nat.gcd d e] := Nat.ModEq.of_dvd hgd h1
    have h2' : p ≡ 1 [MOD Nat.gcd d e] := Nat.ModEq.of_dvd hge h2
    exact h1'.symm.trans h2'
  · intro h
    have hcompat : (n % d) ≡ (1 % e) [MOD Nat.gcd d e] := by
      have hgd : Nat.gcd d e ∣ d := Nat.gcd_dvd_left d e
      have hge : Nat.gcd d e ∣ e := Nat.gcd_dvd_right d e
      have hn : n % d ≡ n [MOD Nat.gcd d e] :=
        Nat.ModEq.of_dvd hgd (Nat.mod_modEq n d)
      have h1 : 1 % e ≡ 1 [MOD Nat.gcd d e] :=
        Nat.ModEq.of_dvd hge (Nat.mod_modEq 1 e)
      exact hn.trans (h.trans h1.symm)
    obtain ⟨k, hk1, hk2⟩ :=
      Nat.chineseRemainder' (n := d) (m := e) (a := n % d) (b := 1 % e) hcompat
    refine ⟨k, ?_, ?_⟩
    · have hk : k % d = (n % d) % d := hk1
      simpa [Nat.mod_mod] using hk
    · have hk : k % e = (1 % e) % e := hk2
      simpa [Nat.mod_mod] using hk
