import Mathlib

theorem Conjectures.Goldbach.BeaumontResonanceWindow :
    ∀ n p q : ℕ, 0 < n → n ≤ p+q → p+q < 2*n → (n ∣ p+q ↔ p+q=n) := by
  intro n p q hn hge hlt
  constructor
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        omega
      · exact hpos
    have hklt : k < 2 := by
      have h : n * k < 2 * n := by simpa [hk] using hlt
      rw [Nat.mul_comm 2 n] at h
      exact Nat.lt_of_mul_lt_mul_left h
    have hk1 : k = 1 := by omega
    simpa [hk1] using hk
  · intro h
    rw [h]
