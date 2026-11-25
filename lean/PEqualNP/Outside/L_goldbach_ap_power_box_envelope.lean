import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_power_box_envelope : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k; let S := fun n : ℕ => (Finset.range (n+1)) ∩ (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)); ∀ n k : ℕ, 2≤n → k≤n → 0≤h k ∧ h k ≤ (if k∈S n then Real.log (n:ℝ) else 0) := by
  dsimp only
  intro n k hn hk
  have hlogn : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  by_cases hprime : Nat.Prime k
  · have hv : ArithmeticFunction.vonMangoldt k = Real.log (k:ℝ) :=
      ArithmeticFunction.vonMangoldt_apply_prime hprime
    have hw : (if Nat.Prime k then Real.log (k:ℝ) else 0) = Real.log (k:ℝ) := if_pos hprime
    have hh : ArithmeticFunction.vonMangoldt k - (if Nat.Prime k then Real.log (k:ℝ) else 0) = 0 := by
      rw [hv, hw, sub_self]
    constructor
    · rw [hh]
    · rw [hh]
      split_ifs with hmem
      · exact hlogn
      · exact le_refl 0
  · by_cases hpp : IsPrimePow k
    · obtain ⟨p, a, hp, ha, hka⟩ := (isPrimePow_nat_iff k).1 hpp
      have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.1 ha
      have hv : ArithmeticFunction.vonMangoldt k = Real.log (p:ℝ) := by
        rw [← hka, ArithmeticFunction.vonMangoldt_apply_pow ha0,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hw : (if Nat.Prime k then Real.log (k:ℝ) else 0) = 0 := by rw [if_neg hprime]
      have hh : ArithmeticFunction.vonMangoldt k - (if Nat.Prime k then Real.log (k:ℝ) else 0)
          = Real.log (p:ℝ) := by rw [hv, hw, sub_zero]
      have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have ha2 : 2 ≤ a := by
        rcases lt_or_ge a 2 with h | h
        · exfalso
          apply hprime
          have ha1 : a = 1 := by omega
          rw [← hka, ha1, pow_one]
          exact hp
        · exact h
      have hkS : k ∈ Finset.range (n+1) ∩
          (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image
            (fun z => z.1 ^ z.2)) := by
        rw [Finset.mem_inter]
        constructor
        · rw [Finset.mem_range]; omega
        · rw [Finset.mem_image]
          refine ⟨(p, a), ?_, hka⟩
          rw [Finset.product_eq_sprod, Finset.mem_product]
          constructor
          · rw [Finset.mem_Icc]
            refine ⟨hp.two_le, ?_⟩
            rw [Nat.le_sqrt]
            calc p * p = p ^ 2 := by ring
              _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha2
              _ = k := hka
              _ ≤ n := hk
          · rw [Finset.mem_Icc]
            refine ⟨ha2, ?_⟩
            exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by
              calc 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp.two_le a
                _ = k := hka
                _ ≤ n := hk)
      have hpk : p ≤ k := by
        have h1 : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
        simpa [hka] using h1
      constructor
      · rw [hh]; exact hlogp
      · rw [hh, if_pos hkS]
        exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast le_trans hpk hk)
    · have hv : ArithmeticFunction.vonMangoldt k = 0 := by
        rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp]
      have hw : (if Nat.Prime k then Real.log (k:ℝ) else 0) = 0 := by rw [if_neg hprime]
      have hh : ArithmeticFunction.vonMangoldt k - (if Nat.Prime k then Real.log (k:ℝ) else 0) = 0 := by
        rw [hv, hw, sub_self]
      constructor
      · rw [hh]
      · rw [hh]
        split_ifs with hmem
        · exact hlogn
        · exact le_refl 0