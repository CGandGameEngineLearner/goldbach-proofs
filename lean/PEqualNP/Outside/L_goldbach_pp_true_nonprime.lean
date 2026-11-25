import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_true_nonprime :
    ∀ p a : ℕ, p.Prime → 2 ≤ a → ¬ Nat.Prime (p ^ a) := by
  intro p a _ ha
  exact Nat.Prime.not_prime_pow ha
