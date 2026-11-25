import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_11_23 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1352078)+1144066*(∑ i,b i)≤(∑ i,Nat.choose (b i) 11)+q*26313518 := by
  intro q b
  have key : ∀ x : ℕ, 1352078 + 1144066*x ≤ Nat.choose x 11 + 26313518 := by
    intro x
    by_cases hx : x < 23
    · interval_cases x <;> decide
    · have hx2 : 23 ≤ x := by omega
      refine Nat.le_induction ?_ ?_ x hx2
      · decide
      · intro n hn ih
        have hmono : 1144066 ≤ Nat.choose n 10 := by
          have hC : Nat.choose 23 10 = 1144066 := by decide
          have h := Nat.choose_le_choose 10 hn
          linarith
        have hch : Nat.choose (n+1) 11 = Nat.choose n 10 + Nat.choose n 11 :=
          Nat.choose_succ_succ' n 10
        linarith
  calc (q*1352078)+1144066*(∑ i, b i) = ∑ i : Fin q, (1352078 + 1144066*(b i)) := by
        rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [smul_eq_mul]
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 26313518) := Finset.sum_le_sum (fun i _ => key (b i))
    _ = (∑ i, Nat.choose (b i) 11)+q*26313518 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
