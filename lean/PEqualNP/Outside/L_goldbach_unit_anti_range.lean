import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_anti_range :
    ∀ n a b : ℕ, 0 < a → a < n → 0 < b → b < n → (n ∣ a + b ↔ a + b = n) := by
  intro n a b ha han hb hbn
  have hlt : a + b < n * 2 := by omega
  constructor
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        rw [Nat.mul_zero] at hk
        omega
      · exact h
    have hklt : k < 2 := by
      by_contra h
      have h2 : 2 ≤ k := by omega
      have hle : n * 2 ≤ n * k := Nat.mul_le_mul_left n h2
      rw [← hk] at hle
      omega
    have hk1 : k = 1 := by omega
    rw [hk1, Nat.mul_one] at hk
    exact hk
  · intro h
    exact ⟨1, by rw [h, Nat.mul_one]⟩
