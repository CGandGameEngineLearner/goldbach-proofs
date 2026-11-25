import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_9 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*9)+36*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*324 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 8 + Nat.choose k 7 = Nat.choose (k + 1) 8 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 7 + Nat.choose k 6 = Nat.choose (k + 1) 7 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 36 ≤ Nat.choose (9 + y) 7 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (9 + y)
      show 36 ≤ Nat.choose (9 + y + 1) 7
      omega
  have hpw : ∀ x : ℕ, 9 + 36 * x ≤ Nat.choose x 8 + 324 := by
    intro x
    rcases Nat.lt_or_ge x 9 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 9 + y := ⟨x - 9, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (9 + y)
        have hm := hmono y
        show 9 + 36 * (9 + y + 1) ≤ Nat.choose (9 + y + 1) 8 + 324
        calc 9 + 36 * (9 + y + 1)
            = (9 + 36 * (9 + y)) + 36 := by ring
          _ ≤ (Nat.choose (9 + y) 8 + 324) + 36 :=
              Nat.add_le_add_right ih 36
          _ ≤ (Nat.choose (9 + y) 8 + 324) + Nat.choose (9 + y) 7 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (9 + y + 1) 8 + 324 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 9 + 36 * ∑ i, b i
      = ∑ i, (9 + 36 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 8 + 324) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 8 + q * 324 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
