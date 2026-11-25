import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1129 :
    ∀ n : ℕ, 1129 ∣ n ^ 2 + 1 ↔ n % 1129 = 168 ∨ n % 1129 = 961 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1129) = (n : ZMod 1129) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((168 : ℕ) : ZMod 1129) ^ 2 + 1 = 0 := by decide
  have hn : ((961 : ℕ) : ZMod 1129) = -((168 : ℕ) : ZMod 1129) := by decide
  have hq : Nat.Prime 1129 := by norm_num
  have hroots : ∀ x : ZMod 1129, x ^ 2 + 1 = 0 ↔
      x = ((168 : ℕ) : ZMod 1129) ∨ x = ((961 : ℕ) : ZMod 1129) := by
    intro x
    haveI : Fact (Nat.Prime 1129) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((168 : ℕ) : ZMod 1129)) * (x + ((168 : ℕ) : ZMod 1129)) = 0 := by
        calc (x - ((168 : ℕ) : ZMod 1129)) * (x + ((168 : ℕ) : ZMod 1129))
            = x ^ 2 + 1 - (((168 : ℕ) : ZMod 1129) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1129 → ((n : ZMod 1129) = ((r : ℕ) : ZMod 1129) ↔ n % 1129 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1129 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1129) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1129).symm
  rw [hd, hcast, hroots, hmem 168 (by decide), hmem 961 (by decide)]

