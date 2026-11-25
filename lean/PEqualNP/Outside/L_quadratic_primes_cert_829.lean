import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_829 :
    ∀ n : ℕ, 829 ∣ n ^ 2 + 1 ↔ n % 829 = 246 ∨ n % 829 = 583 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 829) = (n : ZMod 829) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((246 : ℕ) : ZMod 829) ^ 2 + 1 = 0 := by decide
  have hn : ((583 : ℕ) : ZMod 829) = -((246 : ℕ) : ZMod 829) := by decide
  have hq : Nat.Prime 829 := by norm_num
  have hroots : ∀ x : ZMod 829, x ^ 2 + 1 = 0 ↔
      x = ((246 : ℕ) : ZMod 829) ∨ x = ((583 : ℕ) : ZMod 829) := by
    intro x
    haveI : Fact (Nat.Prime 829) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((246 : ℕ) : ZMod 829)) * (x + ((246 : ℕ) : ZMod 829)) = 0 := by
        calc (x - ((246 : ℕ) : ZMod 829)) * (x + ((246 : ℕ) : ZMod 829))
            = x ^ 2 + 1 - (((246 : ℕ) : ZMod 829) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 829 → ((n : ZMod 829) = ((r : ℕ) : ZMod 829) ↔ n % 829 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 829 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 829) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 829).symm
  rw [hd, hcast, hroots, hmem 246 (by decide), hmem 583 (by decide)]

