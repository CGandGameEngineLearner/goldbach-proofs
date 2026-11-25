import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+10*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*100 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 10 + Nat.choose k 9 = Nat.choose (k + 1) 10 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 9 + Nat.choose k 8 = Nat.choose (k + 1) 9 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 10 ≤ Nat.choose (10 + y) 9 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (10 + y)
      show 10 ≤ Nat.choose (10 + y + 1) 9
      omega
  have hpw : ∀ x : ℕ, 1 + 10 * x ≤ Nat.choose x 10 + 100 := by
    intro x
    rcases Nat.lt_or_ge x 10 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 10 + y := ⟨x - 10, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (10 + y)
        have hm := hmono y
        show 1 + 10 * (10 + y + 1) ≤ Nat.choose (10 + y + 1) 10 + 100
        calc 1 + 10 * (10 + y + 1)
            = (1 + 10 * (10 + y)) + 10 := by ring
          _ ≤ (Nat.choose (10 + y) 10 + 100) + 10 :=
              Nat.add_le_add_right ih 10
          _ ≤ (Nat.choose (10 + y) 10 + 100) + Nat.choose (10 + y) 9 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (10 + y + 1) 10 + 100 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 1 + 10 * ∑ i, b i
      = ∑ i, (1 + 10 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 10 + 100) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 10 + q * 100 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
