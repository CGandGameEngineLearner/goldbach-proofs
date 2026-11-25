import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_radical_cells_lower :
    ∀ n d : ℕ, Nat.gcd n 105 = d → d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 15 ∨ d = 21 ∨ d = 35 ∨ d = 105 := by
  intro n d h
  subst h
  have hdvd : Nat.gcd n 105 ∣ 105 := Nat.gcd_dvd_right n 105
  have hle : Nat.gcd n 105 ≤ 105 := Nat.le_of_dvd (by decide) hdvd
  have hfin : ∀ k : Fin 106, k.val ∣ 105 →
      k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 7 ∨ k.val = 15 ∨ k.val = 21 ∨ k.val = 35 ∨ k.val = 105 := by
    decide
  exact hfin ⟨Nat.gcd n 105, Nat.lt_succ_of_le hle⟩ hdvd
