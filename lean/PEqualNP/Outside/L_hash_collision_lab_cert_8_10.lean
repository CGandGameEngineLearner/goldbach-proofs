import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*45)+120*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*1200 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 8 + Nat.choose k 7 = Nat.choose (k + 1) 8 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 7 + Nat.choose k 6 = Nat.choose (k + 1) 7 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 120 ≤ Nat.choose (10 + y) 7 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (10 + y)
      show 120 ≤ Nat.choose (10 + y + 1) 7
      omega
  have hpw : ∀ x : ℕ, 45 + 120 * x ≤ Nat.choose x 8 + 1200 := by
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
        show 45 + 120 * (10 + y + 1) ≤ Nat.choose (10 + y + 1) 8 + 1200
        calc 45 + 120 * (10 + y + 1)
            = (45 + 120 * (10 + y)) + 120 := by ring
          _ ≤ (Nat.choose (10 + y) 8 + 1200) + 120 :=
              Nat.add_le_add_right ih 120
          _ ≤ (Nat.choose (10 + y) 8 + 1200) + Nat.choose (10 + y) 7 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (10 + y + 1) 8 + 1200 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 45 + 120 * ∑ i, b i
      = ∑ i, (45 + 120 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 8 + 1200) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 8 + q * 1200 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
