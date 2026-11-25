import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_characters_primitive_parity :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ χ : DirichletCharacter ℂ n, χ (-1) = -1 → χ.primitiveCharacter (-1) = -1 := by
  intro n _ _hn χ hχ
  have h : χ.primitiveCharacter (-1) = χ (-1) := by
    simpa using (χ.primitiveCharacter_apply_of_isCoprime (a := (-1 : ℤ)) (by simp))
  exact h.trans hχ
