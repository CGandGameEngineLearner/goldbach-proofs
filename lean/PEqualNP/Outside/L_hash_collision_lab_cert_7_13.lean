import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_7_13 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 1716) + 1716 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 7) + q * 22308 := by
  intro q b
  -- The supporting line through the tight values at load 13 and 14.
  have hsmall : ∀ m : ℕ, m ≤ 13 → 1716 + 1716 * m ≤ Nat.choose m 7 + 22308 := by
    intro m hm
    rcases Nat.lt_or_ge m 13 with h | h
    · omega
    · have h13 : m = 13 := by omega
      subst h13
      norm_num [Nat.choose]
  have hpt : ∀ m : ℕ, 1716 + 1716 * m ≤ Nat.choose m 7 + 22308 := by
    intro m
    rcases Nat.lt_or_ge m 14 with hm | hm
    · exact hsmall m (by omega)
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        1716 + 1716 * 14 ≤ Nat.choose 14 7 + 22308) ?step m hm
      intro n hn ih
      have h6 : 1716 ≤ Nat.choose n 6 :=
        le_trans (by norm_num [Nat.choose] : 1716 ≤ Nat.choose 13 6) (Nat.choose_le_choose 6 (by omega))
      have hrec : Nat.choose (n + 1) 7 = Nat.choose n 6 + Nat.choose n 7 := by
        simpa using Nat.choose_succ_succ n 6
      calc 1716 + 1716 * (n + 1) = (1716 + 1716 * n) + 1716 := by ring
        _ ≤ (Nat.choose n 7 + 22308) + 1716 := Nat.add_le_add_right ih 1716
        _ ≤ (Nat.choose n 7 + 22308) + Nat.choose n 6 := Nat.add_le_add_left h6 _
        _ = Nat.choose (n + 1) 7 + 22308 := by rw [hrec]; ring
  have hsum : (∑ i : Fin q, (1716 + 1716 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 7 + 22308) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (1716 + 1716 * b i)) = q * 1716 + 1716 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 7 + 22308))
      = (∑ i, Nat.choose (b i) 7) + q * 22308 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 1716) + 1716 * (∑ i, b i)
      = ∑ i : Fin q, (1716 + 1716 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 7 + 22308) := hsum
    _ = (∑ i, Nat.choose (b i) 7) + q * 22308 := hright
