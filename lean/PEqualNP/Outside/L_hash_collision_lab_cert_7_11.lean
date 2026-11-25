import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_7_11 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 330) + 462 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 7) + q * 5082 := by
  intro q b
  -- A discrete supporting line, tight at load 11 and 12, summed over the buckets.
  have hpt : ∀ m : ℕ, 330 + 462 * m ≤ Nat.choose m 7 + 5082 := by
    intro m
    rcases Nat.lt_or_ge m 12 with hm | hm
    · interval_cases m <;> norm_num [Nat.choose]
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        330 + 462 * 12 ≤ Nat.choose 12 7 + 5082) ?step m hm
      intro n hn ih
      have h6 : 924 ≤ Nat.choose n 6 :=
        le_trans (by norm_num [Nat.choose] : 924 ≤ Nat.choose 12 6) (Nat.choose_le_choose 6 hn)
      have hrec : Nat.choose (n + 1) 7 = Nat.choose n 6 + Nat.choose n 7 := by
        simpa using Nat.choose_succ_succ n 6
      rw [hrec]
      have h462 : 462 ≤ Nat.choose n 6 := le_trans (by norm_num : 462 ≤ 924) h6
      calc 330 + 462 * (n + 1) = (330 + 462 * n) + 462 := by ring
        _ ≤ (Nat.choose n 7 + 5082) + 462 := Nat.add_le_add_right ih 462
        _ ≤ (Nat.choose n 7 + 5082) + Nat.choose n 6 := Nat.add_le_add (le_refl _) h462
        _ = Nat.choose n 6 + Nat.choose n 7 + 5082 := by ring
  have hsum : (∑ i : Fin q, (330 + 462 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 7 + 5082) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (330 + 462 * b i)) = q * 330 + 462 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 7 + 5082))
      = (∑ i, Nat.choose (b i) 7) + q * 5082 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 330) + 462 * (∑ i, b i)
      = ∑ i : Fin q, (330 + 462 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 7 + 5082) := hsum
    _ = (∑ i, Nat.choose (b i) 7) + q * 5082 := hright
