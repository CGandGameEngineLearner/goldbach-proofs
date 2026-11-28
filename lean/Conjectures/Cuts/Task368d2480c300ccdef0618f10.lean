import Mathlib

theorem Conjectures.Cuts.Task368d2480c300ccdef0618f10 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => (∑ x2 ∈ Finset.range (x1 + (1 : ℕ)) with Nat.Prime x2 ∧ Odd x2 ∧ Nat.Prime (x1 - x2) ∧ Odd (x1 - x2), Real.log ↑x2 * Real.log ↑(x1 - x2)) / ↑x1; let x2 : ℕ → Prop := fun (x2 : ℕ) => (0 : ℕ) < {x3 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Odd x3 ∧ Nat.Prime (x2 - x3) ∧ Odd (x2 - x3)}.card; ∀ (x3 : Finset ℕ), (∑ x4 ∈ x3, x1 x4) ^ (2 : ℕ) ≤ ↑(Finset.filter x2 x3).card * ∑ x4 ∈ x3, x1 x4 ^ (2 : ℕ)) := by
  let pairs (n : ℕ) := (Finset.range (n + 1)).filter
    (fun p => Nat.Prime p ∧ Odd p ∧ Nat.Prime (n - p) ∧ Odd (n - p))
  let w (n : ℕ) : ℝ := (∑ p ∈ pairs n, Real.log p * Real.log (n - p : ℕ)) / n
  intro weight represented s
  let t := s.filter (fun n => 0 < (pairs n).card)
  change (∑ n ∈ s, w n) ^ 2 ≤ (t.card : ℝ) * ∑ n ∈ s, w n ^ 2
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hsum : ∑ n ∈ t, w n = ∑ n ∈ s, w n := by
    apply Finset.sum_subset hsub
    intro n hn hnt
    have h : ¬ 0 < (pairs n).card := fun hp => hnt (Finset.mem_filter.mpr ⟨hn, hp⟩)
    have he : pairs n = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    simp [w, he]
  rw [← hsum]
  apply (sq_sum_le_card_mul_sum_sq (s := t) (f := w)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
