import Mathlib

-- These five primes cover every even residue modulo 210.
set_option maxRecDepth 4096 in
private theorem evenResidueCover : ∀ a : Fin 210, a.val % 2 = 0 →
    Nat.Coprime (a.val + 210 - 3) 210 ∨ Nat.Coprime (a.val + 210 - 5) 210 ∨
    Nat.Coprime (a.val + 210 - 7) 210 ∨ Nat.Coprime (a.val + 210 - 11) 210 ∨
    Nat.Coprime (a.val + 210 - 19) 210 := by
  decide

theorem PEqualNP.Outside.L_goldbach_finite_rough_candidate_lift :
    ∀ n : ℕ, 22 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
  intro n hn heven
  have hparity : n % 210 % 2 = 0 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have lift (p : ℕ) (hp : Nat.Prime p) (hp19 : p ≤ 19)
      (hc : Nat.Coprime (n % 210 + 210 - p) 210) :
      ∃ q : ℕ, Nat.Prime q ∧ q < n ∧ 2 ≤ n - q ∧ Nat.Coprime (n - q) 210 := by
    refine ⟨p, hp, by omega, by omega, ?_⟩
    have hshift : n - p + 210 = (n % 210 + 210 - p) + 210 * (n / 210) := by omega
    have hmod : (n - p) % 210 = (n % 210 + 210 - p) % 210 := by
      simpa only [Nat.add_mod_right, Nat.add_mul_mod_self_left] using
        congrArg (fun x : ℕ => x % 210) hshift
    rw [Nat.coprime_iff_gcd_eq_one] at hc ⊢
    calc
      Nat.gcd (n - p) 210 = Nat.gcd ((n - p) % 210) 210 :=
        (Nat.gcd_comm _ _).trans (Nat.gcd_rec _ _)
      _ = Nat.gcd ((n % 210 + 210 - p) % 210) 210 := by rw [hmod]
      _ = Nat.gcd (n % 210 + 210 - p) 210 :=
        (Nat.gcd_rec _ _).symm.trans (Nat.gcd_comm _ _)
      _ = 1 := hc
  rcases evenResidueCover ⟨n % 210, Nat.mod_lt _ (by decide)⟩ hparity with h | h | h | h | h
  · exact lift 3 (by decide) (by decide) h
  · exact lift 5 (by decide) (by decide) h
  · exact lift 7 (by decide) (by decide) h
  · exact lift 11 (by decide) (by decide) h
  · exact lift 19 (by decide) (by decide) h
