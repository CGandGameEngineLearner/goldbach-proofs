import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_2_11 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*55)+11*(∑ i,b i)≤(∑ i,Nat.choose (b i) 2)+q*121 := by
  intro q b
  have hstep : ∀ k : ℕ, Nat.choose k 2 + k = Nat.choose (k + 1) 2 := by
    intro k
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    exact Nat.add_comm _ _
  have hpw : ∀ x : ℕ, 55 + 11 * x ≤ Nat.choose x 2 + 121 := by
    intro x
    rcases Nat.lt_or_ge x 11 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 11 + y := ⟨x - 11, by omega⟩
      induction y with
      | zero => decide
      | succ y ih =>
        have hs := hstep (11 + y)
        show 55 + 11 * (11 + y + 1) ≤ Nat.choose (11 + y + 1) 2 + 121
        omega
  calc q * 55 + 11 * ∑ i, b i
      = ∑ i, (55 + 11 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 2 + 121) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 2 + q * 121 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
