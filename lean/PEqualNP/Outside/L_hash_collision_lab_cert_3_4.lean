import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_3_4 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*4)+6*(∑ i,b i)≤(∑ i,Nat.choose (b i) 3)+q*24 := by
  intro q b
  have hstep2 : ∀ k : ℕ, Nat.choose k 2 + k = Nat.choose (k + 1) 2 := by
    intro k
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    exact Nat.add_comm _ _
  have hstep3 : ∀ k : ℕ, Nat.choose k 3 + Nat.choose k 2 = Nat.choose (k + 1) 3 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 6 ≤ Nat.choose (4 + y) 2 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstep2 (4 + y)
      show 6 ≤ Nat.choose (4 + y + 1) 2
      omega
  have hpw : ∀ x : ℕ, 4 + 6 * x ≤ Nat.choose x 3 + 24 := by
    intro x
    rcases Nat.lt_or_ge x 4 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 4 + y := ⟨x - 4, by omega⟩
      induction y with
      | zero => decide
      | succ y ih =>
        have hs3 := hstep3 (4 + y)
        have hm := hmono y
        show 4 + 6 * (4 + y + 1) ≤ Nat.choose (4 + y + 1) 3 + 24
        omega
  calc q * 4 + 6 * ∑ i, b i
      = ∑ i, (4 + 6 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 3 + 24) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 3 + q * 24 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
