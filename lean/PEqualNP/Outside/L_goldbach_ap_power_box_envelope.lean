import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_power_box_envelope :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k - w k;
    let S := fun n : ℕ => (Finset.range (n+1)) ∩
      (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image
        (fun z => z.1 ^ z.2));
    ∀ n k : ℕ, 2 ≤ n → k ≤ n →
      0 ≤ h k ∧ h k ≤ (if k ∈ S n then Real.log (n:ℝ) else 0) := by
  dsimp only
  intro n k hn hkn
  have hmem : IsPrimePow k → ¬ Nat.Prime k →
      k ∈ ((Finset.range (n+1)) ∩
        (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image
          (fun z => z.1 ^ z.2))) := by
    intro hpp hnp
    rw [isPrimePow_def] at hpp
    obtain ⟨p, e, hp, he0, hpe⟩ := hpp
    have hp' : Nat.Prime p := Nat.prime_iff.mpr hp
    have he1 : e ≠ 1 := by
      intro h
      subst h
      rw [pow_one] at hpe
      exact hnp (hpe ▸ hp')
    have he2 : 2 ≤ e := by omega
    have hp2 : 2 ≤ p := hp'.two_le
    refine Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    refine Finset.mem_image.mpr ⟨(p, e), ?_, hpe⟩
    change (p, e) ∈ (Finset.Icc 2 (Nat.sqrt n)) ×ˢ (Finset.Icc 2 (Nat.log 2 n))
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · constructor
      · exact hp2
      · rw [Nat.le_sqrt]
        calc p * p = p^2 := by ring
          _ ≤ p^e := Nat.pow_le_pow_right (by omega : 0 < p) he2
          _ = k := hpe
          _ ≤ n := hkn
    · constructor
      · exact he2
      · apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
        calc 2^e ≤ p^e := Nat.pow_le_pow_left hp2 e
          _ = k := hpe
          _ ≤ n := hkn
  have hvm : Nat.Prime k → ArithmeticFunction.vonMangoldt k = Real.log (k:ℝ) := by
    intro hpk
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpk.isPrimePow, hpk.minFac_eq]
  constructor
  · by_cases hpk : Nat.Prime k
    · rw [if_pos hpk, hvm hpk]
      linarith
    · rw [if_neg hpk]
      simpa using ArithmeticFunction.vonMangoldt_nonneg (n := k)
  · by_cases hpk : Nat.Prime k
    · rw [if_pos hpk, hvm hpk]
      have hln : 0 ≤ Real.log (n:ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      by_cases hS : k ∈ ((Finset.range (n+1)) ∩
          (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image
            (fun z => z.1 ^ z.2)))
      · rw [if_pos hS]
        linarith
      · rw [if_neg hS]
        linarith
    · rw [if_neg hpk, sub_zero]
      by_cases hS : k ∈ ((Finset.range (n+1)) ∩
          (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image
            (fun z => z.1 ^ z.2)))
      · rw [if_pos hS]
        have hln : 0 ≤ Real.log (n:ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        calc ArithmeticFunction.vonMangoldt k ≤ Real.log (k:ℝ) :=
              ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log (n:ℝ) := by
              rcases Nat.eq_zero_or_pos k with h | h
              · subst h
                simpa using hln
              · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hkn)
      · rw [if_neg hS]
        have hzero : ArithmeticFunction.vonMangoldt k = 0 := by
          by_contra hne
          have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
          exact hS (hmem hpp hpk)
        rw [hzero]
