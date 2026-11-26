import Mathlib

/-!
# Quadratic residue certificate for the modulus 1609

The congruence `n ^ 2 + 1 ≡ 0 [MOD 1609]` has exactly the two roots `523` and `1086`.
Indeed `1609 = 523 + 1086` and `523 * 1086 = 1609 * 353 + 1`, so
`(n + 523) * (n + 1086) = (n ^ 2 + 1) + 1609 * (n + 353)`.
Since `1609` is prime, it divides the product exactly when it divides one of the factors.
-/

theorem PEqualNP.Outside.L_quadratic_primes_cert_1609 :
    ∀ n:ℕ, 1609∣n^2+1 ↔ n%1609=523 ∨ n%1609=1086 := by
  intro n
  have hp : Nat.Prime 1609 := by norm_num
  have hd : 1609 ∣ n ^ 2 + 1 ↔ 1609 ∣ (n + 523) * (n + 1086) := by
    constructor
    · intro h
      have hEq : (n + 523) * (n + 1086) = (n ^ 2 + 1) + 1609 * (n + 353) := by ring
      rw [hEq]
      exact dvd_add h (dvd_mul_right _ _)
    · intro h
      have hEq : (n + 523) * (n + 1086) = (n ^ 2 + 1) + 1609 * (n + 353) := by ring
      have hsub : n ^ 2 + 1 = (n + 523) * (n + 1086) - 1609 * (n + 353) := by
        rw [hEq, Nat.add_sub_cancel]
      rw [hsub]
      exact Nat.dvd_sub h (dvd_mul_right _ _)
  have h523 : 1609 ∣ n + 523 ↔ n % 1609 = 1086 := by
    constructor
    · intro h
      have hz : (n + 523) % 1609 = 0 := Nat.mod_eq_zero_of_dvd h
      rw [Nat.add_mod] at hz
      norm_num at hz
      have hr : n % 1609 < 1609 := Nat.mod_lt _ (by norm_num)
      have hsum : n % 1609 + 523 = 1609 := by omega
      omega
    · intro h
      have hz : (n + 523) % 1609 = (n % 1609 + 523) % 1609 := by
        rw [Nat.add_mod]
      rw [h] at hz
      norm_num at hz
      exact Nat.dvd_of_mod_eq_zero hz
  have h1086 : 1609 ∣ n + 1086 ↔ n % 1609 = 523 := by
    constructor
    · intro h
      have hz : (n + 1086) % 1609 = 0 := Nat.mod_eq_zero_of_dvd h
      rw [Nat.add_mod] at hz
      norm_num at hz
      have hr : n % 1609 < 1609 := Nat.mod_lt _ (by norm_num)
      have hsum : n % 1609 + 1086 = 1609 := by omega
      omega
    · intro h
      have hz : (n + 1086) % 1609 = (n % 1609 + 1086) % 1609 := by
        rw [Nat.add_mod]
      rw [h] at hz
      norm_num at hz
      exact Nat.dvd_of_mod_eq_zero hz
  constructor
  · intro h
    rw [hd] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr (h523.1 h)
    · exact Or.inl (h1086.1 h)
  · rintro (h | h)
    · exact hd.2 (dvd_mul_of_dvd_right (h1086.2 h) (n + 523))
    · exact hd.2 (dvd_mul_of_dvd_left (h523.2 h) (n + 1086))
