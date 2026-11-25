import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_2_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*45)+10*(∑ i,b i)≤(∑ i,Nat.choose (b i) 2)+q*100 := by
  intro q b
  have hstep : ∀ k : ℕ, Nat.choose k 2 + k = Nat.choose (k + 1) 2 := by
    intro k
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    exact Nat.add_comm _ _
  have hpw : ∀ x : ℕ, 45 + 10 * x ≤ Nat.choose x 2 + 100 := by
    intro x
    rcases Nat.lt_or_ge x 10 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 10 + y := ⟨x - 10, by omega⟩
      induction y with
      | zero => decide
      | succ y ih =>
        have hs := hstep (10 + y)
        show 45 + 10 * (10 + y + 1) ≤ Nat.choose (10 + y + 1) 2 + 100
        omega
  calc q * 45 + 10 * ∑ i, b i
      = ∑ i, (45 + 10 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 2 + 100) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 2 + q * 100 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
