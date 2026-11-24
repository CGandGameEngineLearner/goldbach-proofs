import Mathlib

theorem PEqualNP.Outside.L_log_rank_adjacent_variance :
    ∀ (n : ℕ) (A : Finset (Fin n)) (Y : Finset (Finset (Fin n))) (a : ℤ), let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; let varY := fun (A : Finset (Fin n)) => let f := fun B : Finset (Fin n) => ((A ∩ B).card : ℝ); let avg := Finset.sum Y f / (Y.card : ℝ); Finset.sum Y (fun B => (f B - avg)^2) / (Y.card : ℝ); Y.Nonempty → (∀ B ∈ Y, adj A B a) → varY A ≤ 1/4 := by
  intro n A Y a adj varY hNE hadj
  classical
  set f : Finset (Fin n) → ℝ := fun B => ((A ∩ B).card : ℝ) with hf
  set m : ℝ := (Y.card : ℝ) with hm
  set S : ℝ := Finset.sum Y f with hS
  have hmpos : 0 < m := by
    rw [hm]
    exact_mod_cast Finset.card_pos.mpr hNE
  have hval : ∀ B ∈ Y, f B = (a : ℝ) ∨ f B = (a : ℝ) + 1 := by
    intro B hB
    have h := hadj B hB
    rcases h with h | h
    · left
      show ((A ∩ B).card : ℝ) = (a : ℝ)
      exact_mod_cast h
    · right
      show ((A ∩ B).card : ℝ) = (a : ℝ) + 1
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      exact h'
  have hsq : ∀ B ∈ Y, f B ^ 2 = (2 * (a : ℝ) + 1) * f B - (a : ℝ) * ((a : ℝ) + 1) := by
    intro B hB
    rcases hval B hB with h | h <;> rw [h] <;> ring
  have hsum_sq : Finset.sum Y (fun B => f B ^ 2) = (2 * (a : ℝ) + 1) * S - m * ((a : ℝ) * ((a : ℝ) + 1)) := by
    rw [Finset.sum_congr rfl hsq, Finset.sum_sub_distrib]
    have hc1 : Finset.sum Y (fun B => (2 * (a : ℝ) + 1) * f B) = (2 * (a : ℝ) + 1) * S := by
      rw [hS]
      exact (Finset.mul_sum Y f (2 * (a : ℝ) + 1)).symm
    have hc2 : Finset.sum Y (fun B => (a : ℝ) * ((a : ℝ) + 1)) = m * ((a : ℝ) * ((a : ℝ) + 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul, hm]
    rw [hc1, hc2]
  have hvar : Finset.sum Y (fun B => (f B - S / m) ^ 2) = Finset.sum Y (fun B => f B ^ 2) - S ^ 2 / m := by
    have hpt : ∀ B ∈ Y, (f B - S / m) ^ 2 = f B ^ 2 - 2 * (S / m) * f B + (S / m) ^ 2 := by
      intro B hB
      ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hc1 : Finset.sum Y (fun B => 2 * (S / m) * f B) = 2 * (S / m) * S := by
      rw [hS]
      exact (Finset.mul_sum Y f (2 * (S / m))).symm
    have hc2 : Finset.sum Y (fun B => (S / m) ^ 2) = m * (S / m) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hm]
    rw [hc1, hc2]
    field_simp
    ring
  have hgoal : varY A = Finset.sum Y (fun B => (f B - S / m) ^ 2) / m := rfl
  rw [hgoal, hvar, hsum_sq]
  have hmain : ((2 * (a : ℝ) + 1) * S - m * ((a : ℝ) * ((a : ℝ) + 1)) - S ^ 2 / m) / m
      = 1 / 4 - (S / m - ((a : ℝ) + 1 / 2)) ^ 2 := by
    field_simp
    ring
  rw [hmain]
  linarith [sq_nonneg (S / m - ((a : ℝ) + 1 / 2))]
