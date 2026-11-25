import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_active_range :
    ∀ k j : ℕ, j≤k → (2 < (2:ℕ)^k/2^j ↔ j+2≤k) := by
  intro k j hjk
  have hpos : 0 < (2:ℕ)^j := by
    have h1 : 1 ≤ (2:ℕ)^j := Nat.one_le_two_pow
    omega
  have hdiv : (2:ℕ)^k / 2^j = 2^(k-j) := by
    apply Nat.div_eq_of_eq_mul_right hpos
    rw [← Nat.pow_add, Nat.add_sub_of_le hjk]
  have hkey : ∀ m : ℕ, (2 < (2:ℕ)^m ↔ 2 ≤ m) := by
    intro m
    constructor
    · intro h
      by_contra hn
      have hle : m ≤ 1 := by omega
      have hp : (2:ℕ)^m ≤ 2^1 := Nat.pow_le_pow_right (n := 2) (by decide) hle
      omega
    · intro h
      have hp : (2:ℕ)^2 ≤ 2^m := Nat.pow_le_pow_right (n := 2) (by decide) h
      omega
  rw [hdiv, hkey (k-j)]
  omega
