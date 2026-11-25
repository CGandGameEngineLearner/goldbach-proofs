import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_18 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*48620)+43758*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*787644 := by
  intro q b
  -- Discrete supporting line for the occupancy count at order 9, tight at loads 18 and 19.
  have hpt : ∀ m : ℕ, 48620 + 43758 * m ≤ Nat.choose m 9 + 787644 := by
    intro m
    rcases Nat.lt_or_ge m 19 with hm | hm
    · interval_cases m <;> norm_num [Nat.choose]
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        48620 + 43758 * 19 ≤ Nat.choose 19 9 + 787644) ?step m hm
      intro n hn ih
      have hn18 : 18 ≤ n := le_trans (by norm_num : 18 ≤ 19) hn
      have hprev : 43758 ≤ Nat.choose n 8 :=
        le_trans (by norm_num [Nat.choose] : 43758 ≤ Nat.choose 18 8)
          (Nat.choose_le_choose 8 hn18)
      have hrec : Nat.choose (n + 1) 9 = Nat.choose n 8 + Nat.choose n 9 := by
        simpa using Nat.choose_succ_succ n 8
      rw [hrec]
      calc 48620 + 43758 * (n + 1) = (48620 + 43758 * n) + 43758 := by ring
        _ ≤ (Nat.choose n 9 + 787644) + 43758 := Nat.add_le_add_right ih 43758
        _ ≤ (Nat.choose n 9 + 787644) + Nat.choose n 8 := Nat.add_le_add (le_refl _) hprev
        _ = Nat.choose n 8 + Nat.choose n 9 + 787644 := by ring
  have hsum : (∑ i : Fin q, (48620 + 43758 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 787644) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (48620 + 43758 * b i)) = q * 48620 + 43758 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 9 + 787644))
      = (∑ i, Nat.choose (b i) 9) + q * 787644 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 48620) + 43758 * (∑ i, b i)
      = ∑ i : Fin q, (48620 + 43758 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 787644) := hsum
    _ = (∑ i, Nat.choose (b i) 9) + q * 787644 := hright
