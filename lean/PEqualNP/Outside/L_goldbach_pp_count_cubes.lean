import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_count_cubes :
    ∀ n : ℕ,
      let s := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ^ 3 ≤ n)
      s.card ^ 3 ≤ n := by
  intro n
  dsimp only
  let s := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ^ 3 ≤ n)
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := Finset.max'_mem s hs
    have hm3 : m ^ 3 ≤ n := (Finset.mem_filter.mp hm).2.2
    have hcard : s.card ≤ m := by
      have hsub : s ⊆ Finset.Icc 1 m := by
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2.1
        have hp1 : 1 ≤ p := hp'.one_le
        have hpm : p ≤ m := Finset.le_max' s p hp
        exact Finset.mem_Icc.mpr ⟨hp1, hpm⟩
      have h := Finset.card_le_card hsub
      simpa [Nat.card_Icc] using h
    calc
      s.card ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hcard 3
      _ ≤ n := hm3
  · have hs0 : s.card = 0 := by
      have h : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [h]
    have hempty : (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ p ^ 3 ≤ n) = ∅ := by
      simpa [s] using (Finset.card_eq_zero.mp hs0)
    simp [hempty]
