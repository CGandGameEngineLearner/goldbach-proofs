import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_5 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+5*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*25 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 5 + Nat.choose k 4 = Nat.choose (k + 1) 5 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 4 + Nat.choose k 3 = Nat.choose (k + 1) 4 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 5 ≤ Nat.choose (5 + y) 4 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (5 + y)
      show 5 ≤ Nat.choose (5 + y + 1) 4
      omega
  have hpw : ∀ x : ℕ, 1 + 5 * x ≤ Nat.choose x 5 + 25 := by
    intro x
    rcases Nat.lt_or_ge x 5 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 5 + y := ⟨x - 5, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (5 + y)
        have hm := hmono y
        show 1 + 5 * (5 + y + 1) ≤ Nat.choose (5 + y + 1) 5 + 25
        calc 1 + 5 * (5 + y + 1)
            = (1 + 5 * (5 + y)) + 5 := by ring
          _ ≤ (Nat.choose (5 + y) 5 + 25) + 5 :=
              Nat.add_le_add_right ih 5
          _ ≤ (Nat.choose (5 + y) 5 + 25) + Nat.choose (5 + y) 4 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (5 + y + 1) 5 + 25 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 1 + 5 * ∑ i, b i
      = ∑ i, (1 + 5 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 5 + 25) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 5 + q * 25 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
