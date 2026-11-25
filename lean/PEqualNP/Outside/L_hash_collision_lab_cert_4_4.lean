import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_4_4 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+4*(∑ i,b i)≤(∑ i,Nat.choose (b i) 4)+q*16 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 4 + Nat.choose k 3 = Nat.choose (k + 1) 4 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 3 + Nat.choose k 2 = Nat.choose (k + 1) 3 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 4 ≤ Nat.choose (4 + y) 3 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (4 + y)
      show 4 ≤ Nat.choose (4 + y + 1) 3
      omega
  have hpw : ∀ x : ℕ, 1 + 4 * x ≤ Nat.choose x 4 + 16 := by
    intro x
    rcases Nat.lt_or_ge x 4 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 4 + y := ⟨x - 4, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (4 + y)
        have hm := hmono y
        show 1 + 4 * (4 + y + 1) ≤ Nat.choose (4 + y + 1) 4 + 16
        calc 1 + 4 * (4 + y + 1)
            = (1 + 4 * (4 + y)) + 4 := by ring
          _ ≤ (Nat.choose (4 + y) 4 + 16) + 4 :=
              Nat.add_le_add_right ih 4
          _ ≤ (Nat.choose (4 + y) 4 + 16) + Nat.choose (4 + y) 3 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (4 + y + 1) 4 + 16 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 1 + 4 * ∑ i, b i
      = ∑ i, (1 + 4 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 4 + 16) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 4 + q * 16 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
