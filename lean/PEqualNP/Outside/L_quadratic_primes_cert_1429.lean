import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1429 :
    ∀ n : ℕ, 1429 ∣ n ^ 2 + 1 ↔ n % 1429 = 620 ∨ n % 1429 = 809 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1429) = (n : ZMod 1429) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((620 : ℕ) : ZMod 1429) ^ 2 + 1 = 0 := by decide
  have hn : ((809 : ℕ) : ZMod 1429) = -((620 : ℕ) : ZMod 1429) := by decide
  have hq : Nat.Prime 1429 := by norm_num
  have hroots : ∀ x : ZMod 1429, x ^ 2 + 1 = 0 ↔
      x = ((620 : ℕ) : ZMod 1429) ∨ x = ((809 : ℕ) : ZMod 1429) := by
    intro x
    haveI : Fact (Nat.Prime 1429) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((620 : ℕ) : ZMod 1429)) * (x + ((620 : ℕ) : ZMod 1429)) = 0 := by
        calc (x - ((620 : ℕ) : ZMod 1429)) * (x + ((620 : ℕ) : ZMod 1429))
            = x ^ 2 + 1 - (((620 : ℕ) : ZMod 1429) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1429 → ((n : ZMod 1429) = ((r : ℕ) : ZMod 1429) ↔ n % 1429 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1429 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1429) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1429).symm
  rw [hd, hcast, hroots, hmem 620 (by decide), hmem 809 (by decide)]

