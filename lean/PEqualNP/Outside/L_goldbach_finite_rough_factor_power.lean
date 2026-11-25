import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.Order.BigOperators.Group.List

theorem PEqualNP.Outside.L_goldbach_finite_rough_factor_power :
    ∀ s y : ℕ, 2 ≤ s → 2 ≤ y → (∀ p, Nat.Prime p → p ∣ s → y ≤ p) → y^(s.primeFactorsList.length) ≤ s := by
  intro s y hs _ h
  calc
    y ^ s.primeFactorsList.length ≤ s.primeFactorsList.prod :=
      List.pow_length_le_prod s.primeFactorsList y (fun p hp => h p (Nat.prime_of_mem_primeFactorsList hp)
        (Nat.dvd_of_mem_primeFactorsList hp))
    _ = s := Nat.prod_primeFactorsList (by omega)
