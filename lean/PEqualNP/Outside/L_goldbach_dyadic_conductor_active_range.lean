import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_active_range :
    ∀ k j : ℕ, j≤k → (2 < (2:ℕ)^k/2^j ↔ j+2≤k) := by
  intro k j hj
  rw [Nat.pow_div hj (by norm_num : 0 < (2:ℕ))]
  constructor
  · intro h
    by_contra hle
    have hexp : k-j ≤ 1 := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hexp
    norm_num at hpow
    omega
  · intro h
    have hexp : 1 < k-j := by omega
    have hpow := Nat.pow_lt_pow_right (by norm_num : 1 < (2:ℕ)) hexp
    simpa using hpow
