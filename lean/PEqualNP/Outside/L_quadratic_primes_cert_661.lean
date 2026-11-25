import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_661 :
    ∀ n : ℕ, 661 ∣ n ^ 2 + 1 ↔ n % 661 = 106 ∨ n % 661 = 555 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 661) = (n : ZMod 661) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((106 : ℕ) : ZMod 661) ^ 2 + 1 = 0 := by decide
  have hn : ((555 : ℕ) : ZMod 661) = -((106 : ℕ) : ZMod 661) := by decide
  have hq : Nat.Prime 661 := by norm_num
  have hroots : ∀ x : ZMod 661, x ^ 2 + 1 = 0 ↔
      x = ((106 : ℕ) : ZMod 661) ∨ x = ((555 : ℕ) : ZMod 661) := by
    intro x
    haveI : Fact (Nat.Prime 661) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((106 : ℕ) : ZMod 661)) * (x + ((106 : ℕ) : ZMod 661)) = 0 := by
        calc (x - ((106 : ℕ) : ZMod 661)) * (x + ((106 : ℕ) : ZMod 661))
            = x ^ 2 + 1 - (((106 : ℕ) : ZMod 661) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 661 → ((n : ZMod 661) = ((r : ℕ) : ZMod 661) ↔ n % 661 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 661 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 661) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 661).symm
  rw [hd, hcast, hroots, hmem 106 (by decide), hmem 555 (by decide)]

