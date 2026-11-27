import Mathlib

theorem Conjectures.TwinPrimes.QuadraticSquareSieveResidues : (∀ ℓ : ℕ, ℓ.Prime → ((Finset.range ℓ).filter fun a => (a=0 ∨ a^2%ℓ=2%ℓ)).card = if ℓ=2 then 1 else 1+((Finset.range ℓ).filter fun a => a^2%ℓ=2%ℓ).card) := by
  intro ℓ hℓ
  split_ifs with h2
  · subst h2
    decide
  · have hℓ3 : 2 < ℓ := by
      have := hℓ.two_le
      omega
    have hsplit : (Finset.range ℓ).filter (fun a => a = 0 ∨ a^2 % ℓ = 2 % ℓ) =
        insert 0 ((Finset.range ℓ).filter fun a => a^2 % ℓ = 2 % ℓ) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨ha, h | h⟩
        · exact Or.inl h
        · exact Or.inr ⟨ha, h⟩
      · rintro (h | ⟨ha, h⟩)
        · exact ⟨by omega, Or.inl h⟩
        · exact ⟨ha, Or.inr h⟩
    rw [hsplit, Finset.card_insert_of_notMem, add_comm]
    simp only [Finset.mem_filter, Finset.mem_range, not_and]
    intro _
    rw [Nat.mod_eq_of_lt hℓ3]
    simp
