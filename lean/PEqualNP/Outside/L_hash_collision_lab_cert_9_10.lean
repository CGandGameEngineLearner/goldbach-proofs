import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*10)+45*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*450 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 9 + Nat.choose k 8 = Nat.choose (k + 1) 9 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 8 + Nat.choose k 7 = Nat.choose (k + 1) 8 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 45 ≤ Nat.choose (10 + y) 8 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (10 + y)
      show 45 ≤ Nat.choose (10 + y + 1) 8
      omega
  have hpw : ∀ x : ℕ, 10 + 45 * x ≤ Nat.choose x 9 + 450 := by
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
        show 10 + 45 * (10 + y + 1) ≤ Nat.choose (10 + y + 1) 9 + 450
        calc 10 + 45 * (10 + y + 1)
            = (10 + 45 * (10 + y)) + 45 := by ring
          _ ≤ (Nat.choose (10 + y) 9 + 450) + 45 :=
              Nat.add_le_add_right ih 45
          _ ≤ (Nat.choose (10 + y) 9 + 450) + Nat.choose (10 + y) 8 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (10 + y + 1) 9 + 450 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 10 + 45 * ∑ i, b i
      = ∑ i, (10 + 45 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 9 + 450) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 9 + q * 450 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
