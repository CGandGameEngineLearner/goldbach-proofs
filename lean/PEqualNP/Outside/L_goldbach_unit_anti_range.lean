theorem L_goldbach_unit_anti_range :
    ∀ n a b : Nat, 0 < a → a < n → 0 < b → b < n →
      (n ∣ a + b ↔ a + b = n) := by
  intro n a b ha han hb hbn
  constructor
  · intro hd
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by
      intro h
      simp [h] at hk
      omega
    have hk2 : ¬ 2 ≤ k := by
      intro h
      have hmul : n * 2 ≤ n * k := Nat.mul_le_mul_left n h
      rw [← hk] at hmul
      omega
    have h1 : k = 1 := by omega
    simpa [h1] using hk
  · intro h
    rw [h]
    exact Nat.dvd_refl n
