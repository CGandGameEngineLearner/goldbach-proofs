import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_853 :
    ∀ n : ℕ, 853 ∣ n ^ 2 + 1 ↔ n % 853 = 333 ∨ n % 853 = 520 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 853) = (n : ZMod 853) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((333 : ℕ) : ZMod 853) ^ 2 + 1 = 0 := by decide
  have hn : ((520 : ℕ) : ZMod 853) = -((333 : ℕ) : ZMod 853) := by decide
  have hq : Nat.Prime 853 := by norm_num
  have hroots : ∀ x : ZMod 853, x ^ 2 + 1 = 0 ↔
      x = ((333 : ℕ) : ZMod 853) ∨ x = ((520 : ℕ) : ZMod 853) := by
    intro x
    haveI : Fact (Nat.Prime 853) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((333 : ℕ) : ZMod 853)) * (x + ((333 : ℕ) : ZMod 853)) = 0 := by
        calc (x - ((333 : ℕ) : ZMod 853)) * (x + ((333 : ℕ) : ZMod 853))
            = x ^ 2 + 1 - (((333 : ℕ) : ZMod 853) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 853 → ((n : ZMod 853) = ((r : ℕ) : ZMod 853) ↔ n % 853 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 853 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 853) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 853).symm
  rw [hd, hcast, hroots, hmem 333 (by decide), hmem 520 (by decide)]

