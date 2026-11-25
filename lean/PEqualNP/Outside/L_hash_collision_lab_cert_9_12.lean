import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_12 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 220) + 495 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 9) + q * 5940 := by
  intro q b
  -- The supporting line through the tight values at load 12 and 13.
  have hsmall : ∀ m : ℕ, m ≤ 12 → 220 + 495 * m ≤ Nat.choose m 9 + 5940 := by
    intro m hm
    rcases Nat.lt_or_ge m 12 with h | h
    · omega
    · have h12 : m = 12 := by omega
      subst h12
      norm_num [Nat.choose]
  have hpt : ∀ m : ℕ, 220 + 495 * m ≤ Nat.choose m 9 + 5940 := by
    intro m
    rcases Nat.lt_or_ge m 13 with hm | hm
    · exact hsmall m (by omega)
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        220 + 495 * 13 ≤ Nat.choose 13 9 + 5940) ?step m hm
      intro n hn ih
      have h6 : 495 ≤ Nat.choose n 8 :=
        le_trans (by norm_num [Nat.choose] : 495 ≤ Nat.choose 12 8) (Nat.choose_le_choose 8 (by omega))
      have hrec : Nat.choose (n + 1) 9 = Nat.choose n 8 + Nat.choose n 9 := by
        simpa using Nat.choose_succ_succ n 8
      calc 220 + 495 * (n + 1) = (220 + 495 * n) + 495 := by ring
        _ ≤ (Nat.choose n 9 + 5940) + 495 := Nat.add_le_add_right ih 495
        _ ≤ (Nat.choose n 9 + 5940) + Nat.choose n 8 := Nat.add_le_add_left h6 _
        _ = Nat.choose (n + 1) 9 + 5940 := by rw [hrec]; ring
  have hsum : (∑ i : Fin q, (220 + 495 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 5940) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (220 + 495 * b i)) = q * 220 + 495 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 9 + 5940))
      = (∑ i, Nat.choose (b i) 9) + q * 5940 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 220) + 495 * (∑ i, b i)
      = ∑ i : Fin q, (220 + 495 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 5940) := hsum
    _ = (∑ i, Nat.choose (b i) 9) + q * 5940 := hright
