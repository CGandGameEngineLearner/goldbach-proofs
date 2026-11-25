import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_16 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 8008) + 11440 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 10) + q * 183040 := by
  intro q b
  -- The supporting line through the tight values at load 16 and 17.
  have hsmall : ∀ m : ℕ, m ≤ 16 → 8008 + 11440 * m ≤ Nat.choose m 10 + 183040 := by
    intro m hm
    rcases Nat.lt_or_ge m 16 with h | h
    · omega
    · have h16 : m = 16 := by omega
      subst h16
      norm_num [Nat.choose]
  have hpt : ∀ m : ℕ, 8008 + 11440 * m ≤ Nat.choose m 10 + 183040 := by
    intro m
    rcases Nat.lt_or_ge m 17 with hm | hm
    · exact hsmall m (by omega)
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        8008 + 11440 * 17 ≤ Nat.choose 17 10 + 183040) ?step m hm
      intro n hn ih
      have h6 : 11440 ≤ Nat.choose n 9 :=
        le_trans (by norm_num [Nat.choose] : 11440 ≤ Nat.choose 16 9) (Nat.choose_le_choose 9 (by omega))
      have hrec : Nat.choose (n + 1) 10 = Nat.choose n 9 + Nat.choose n 10 := by
        simpa using Nat.choose_succ_succ n 9
      calc 8008 + 11440 * (n + 1) = (8008 + 11440 * n) + 11440 := by ring
        _ ≤ (Nat.choose n 10 + 183040) + 11440 := Nat.add_le_add_right ih 11440
        _ ≤ (Nat.choose n 10 + 183040) + Nat.choose n 9 := Nat.add_le_add_left h6 _
        _ = Nat.choose (n + 1) 10 + 183040 := by rw [hrec]; ring
  have hsum : (∑ i : Fin q, (8008 + 11440 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 183040) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (8008 + 11440 * b i)) = q * 8008 + 11440 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 10 + 183040))
      = (∑ i, Nat.choose (b i) 10) + q * 183040 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 8008) + 11440 * (∑ i, b i)
      = ∑ i : Fin q, (8008 + 11440 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 183040) := hsum
    _ = (∑ i, Nat.choose (b i) 10) + q * 183040 := hright
