import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_partial_period :
    ∀ (q X a : ℕ), a < q →
      ((Finset.range X).filter (fun k => k % q = a)).card ≤ X / q + 1 := by
  intro q X a _ha
  -- Within a single residue class the quotient uniquely identifies each index.
  calc
    _ ≤ (Finset.range (X / q + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun k : ℕ => k / q)
      · intro k hk
        have hkX := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hkX.le))
      · intro i hi j hj hij
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        change i / q = j / q at hij
        calc
          i = i % q + q * (i / q) := (Nat.mod_add_div i q).symm
          _ = j % q + q * (j / q) := by rw [hi', hj', hij]
          _ = j := Nat.mod_add_div j q
    _ = _ := Finset.card_range _
