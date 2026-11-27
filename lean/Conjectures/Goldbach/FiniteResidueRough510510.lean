import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.FiniteResidueRough510510 :
    ∀ a : ℕ, a < 510510 → Even a → ∃ p ∈ ({3,5,7,11,41,61,79,149,167,769,1747,2297,2311} : Finset ℕ), Nat.Coprime ((a+510510-p)%510510) 510510 := by
  have h : ∀ x : Fin 510510, Even (x : ℕ) →
      ∃ p ∈ ({3,5,7,11,41,61,79,149,167,769,1747,2297,2311} : Finset ℕ),
        Nat.Coprime (((x : ℕ)+510510-p)%510510) 510510 := by
    native_decide
  intro a ha he
  exact h ⟨a, ha⟩ he
