import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_insert :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ), x∉S → (ok (insert x S) ↔ ok S ∧ ∀ a∈S, ∀ b∈S,a≠b → d a b x≠0) := by
  dsimp only
  intro S x hxS
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha b hb c hc hab hbc hac
      exact h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hab hbc hac
    · intro a ha b hb hab
      have hax : a ≠ x := fun hEq => hxS (hEq ▸ ha)
      have hbx : b ≠ x := fun hEq => hxS (hEq ▸ hb)
      exact h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) x (Finset.mem_insert_self x S) hab hbx hax
  · rintro ⟨hok, hsec⟩ a ha b hb c hc hab hbc hac
    rcases Finset.mem_insert.mp ha with rfl | haS
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact absurd rfl hab
      · rcases Finset.mem_insert.mp hc with rfl | hcS
        · exact absurd rfl hac
        · intro h0
          exact hsec b hbS c hcS hbc (by linear_combination h0)
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · rcases Finset.mem_insert.mp hc with rfl | hcS
        · exact absurd rfl hbc
        · intro h0
          exact hsec a haS c hcS hac (by linear_combination -h0)
      · rcases Finset.mem_insert.mp hc with rfl | hcS
        · exact hsec a haS b hbS hab
        · exact hok a haS b hbS c hcS hab hbc hac
