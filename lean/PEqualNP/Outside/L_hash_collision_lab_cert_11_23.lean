import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_11_23 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1352078)+1144066*(∑ i,b i)≤(∑ i,Nat.choose (b i) 11)+q*26313518 := by
  intro q b
  -- Discrete supporting line for the occupancy count at order 11, tight at loads 23 and 24.
  have hpt : ∀ m : ℕ, 1352078 + 1144066 * m ≤ Nat.choose m 11 + 26313518 := by
    intro m
    rcases Nat.lt_or_ge m 24 with hm | hm
    · interval_cases m <;> norm_num [Nat.choose]
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        1352078 + 1144066 * 24 ≤ Nat.choose 24 11 + 26313518) ?step m hm
      intro n hn ih
      have hn23 : 23 ≤ n := le_trans (by norm_num : 23 ≤ 24) hn
      have hprev : 1144066 ≤ Nat.choose n 10 :=
        le_trans (by norm_num [Nat.choose] : 1144066 ≤ Nat.choose 23 10)
          (Nat.choose_le_choose 10 hn23)
      have hrec : Nat.choose (n + 1) 11 = Nat.choose n 10 + Nat.choose n 11 := by
        simpa using Nat.choose_succ_succ n 10
      rw [hrec]
      calc 1352078 + 1144066 * (n + 1) = (1352078 + 1144066 * n) + 1144066 := by ring
        _ ≤ (Nat.choose n 11 + 26313518) + 1144066 := Nat.add_le_add_right ih 1144066
        _ ≤ (Nat.choose n 11 + 26313518) + Nat.choose n 10 := Nat.add_le_add (le_refl _) hprev
        _ = Nat.choose n 10 + Nat.choose n 11 + 26313518 := by ring
  have hsum : (∑ i : Fin q, (1352078 + 1144066 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 26313518) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (1352078 + 1144066 * b i))
      = q * 1352078 + 1144066 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 11 + 26313518))
      = (∑ i, Nat.choose (b i) 11) + q * 26313518 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 1352078) + 1144066 * (∑ i, b i)
      = ∑ i : Fin q, (1352078 + 1144066 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 26313518) := hsum
    _ = (∑ i, Nat.choose (b i) 11) + q * 26313518 := hright
