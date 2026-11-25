import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_733 :
    ∀ n : ℕ, 733 ∣ n ^ 2 + 1 ↔ n % 733 = 353 ∨ n % 733 = 380 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 733) = (n : ZMod 733) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((353 : ℕ) : ZMod 733) ^ 2 + 1 = 0 := by decide
  have hn : ((380 : ℕ) : ZMod 733) = -((353 : ℕ) : ZMod 733) := by decide
  have hq : Nat.Prime 733 := by norm_num
  have hroots : ∀ x : ZMod 733, x ^ 2 + 1 = 0 ↔
      x = ((353 : ℕ) : ZMod 733) ∨ x = ((380 : ℕ) : ZMod 733) := by
    intro x
    haveI : Fact (Nat.Prime 733) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((353 : ℕ) : ZMod 733)) * (x + ((353 : ℕ) : ZMod 733)) = 0 := by
        calc (x - ((353 : ℕ) : ZMod 733)) * (x + ((353 : ℕ) : ZMod 733))
            = x ^ 2 + 1 - (((353 : ℕ) : ZMod 733) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 733 → ((n : ZMod 733) = ((r : ℕ) : ZMod 733) ↔ n % 733 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 733 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 733) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 733).symm
  rw [hd, hcast, hroots, hmem 353 (by decide), hmem 380 (by decide)]

