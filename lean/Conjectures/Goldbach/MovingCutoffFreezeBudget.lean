import Mathlib

theorem Conjectures.Goldbach.MovingCutoffFreezeBudget :
    ∀ (I : Finset ℕ) (K : ℕ) (b : ℕ → ℕ) (f : ℕ → ℂ) (r y : ℕ → ℝ) (G : ℕ → ℝ → ℂ), (∀ m ∈ I, b m < K) → (∀ m ∈ I, ‖f m‖ ≤ 1) → let B : ℕ → Finset ℕ := fun j => I.filter (fun m => b m = j); ‖∑ m ∈ I, f m * G m (r m)‖ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ j ∈ Finset.range K, ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖ ∧ (∑ j ∈ Finset.range K, Real.sqrt ((B j).card : ℝ)) ≤ Real.sqrt (K : ℝ) * Real.sqrt (I.card : ℝ) := by
  intro I K b f r y G hb hf
  dsimp only
  refine ⟨?_, ?_⟩
  · have hfib : (∑ m ∈ I, f m * G m (r m)) =
        ∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j), f m * G m (r m) := by
      exact (Finset.sum_fiberwise_of_maps_to (g := b) (s := I) (t := Finset.range K)
        (fun m hm => Finset.mem_range.mpr (hb m hm)) (fun m => f m * G m (r m))).symm
    have hdec : ∀ j : ℕ, (∑ m ∈ I.filter (fun m => b m = j), f m * G m (r m)) =
        (∑ m ∈ I.filter (fun m => b m = j), f m * G m (y j)) +
          ∑ m ∈ I.filter (fun m => b m = j), f m * (G m (r m) - G m (y j)) := by
      intro j
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    have hsplit : (∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
        f m * G m (r m)) =
        (∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j), f m * G m (y j)) +
          ∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
            f m * (G m (r m) - G m (y j)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => hdec j)
    calc ‖∑ m ∈ I, f m * G m (r m)‖
        = ‖∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j), f m * G m (r m)‖ := by
          rw [hfib]
      _ = ‖(∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j), f m * G m (y j)) +
            ∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
              f m * (G m (r m) - G m (y j))‖ := by
          rw [hsplit]
      _ ≤ ‖∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j), f m * G m (y j)‖ +
            ‖∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
              f m * (G m (r m) - G m (y j))‖ := norm_add_le _ _
      _ ≤ (∑ j ∈ Finset.range K, ‖∑ m ∈ I.filter (fun m => b m = j), f m * G m (y j)‖) +
            ∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
              ‖G m (r m) - G m (y j)‖ := by
          refine add_le_add (norm_sum_le _ _) ?_
          calc ‖∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
                  f m * (G m (r m) - G m (y j))‖
              ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ I.filter (fun m => b m = j),
                  f m * (G m (r m) - G m (y j))‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range K, ∑ m ∈ I.filter (fun m => b m = j),
                  ‖G m (r m) - G m (y j)‖ :=
                Finset.sum_le_sum (fun j _ =>
                  le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun m hm => by
                    have hmem : m ∈ I := (Finset.mem_filter.mp hm).1
                    calc ‖f m * (G m (r m) - G m (y j))‖
                        = ‖f m‖ * ‖G m (r m) - G m (y j)‖ := norm_mul _ _
                      _ ≤ 1 * ‖G m (r m) - G m (y j)‖ :=
                          mul_le_mul_of_nonneg_right (hf m hmem) (norm_nonneg _)
                      _ = ‖G m (r m) - G m (y j)‖ := one_mul _)))
  · have hcard : (I.card : ℝ) =
        ∑ j ∈ Finset.range K, ((I.filter (fun m => b m = j)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (f := b) (s := I)
        (t := Finset.range K) (fun m hm => Finset.mem_range.mpr (hb m hm))
    have hcs : (∑ j ∈ Finset.range K,
        Real.sqrt ((I.filter (fun m => b m = j)).card : ℝ)) ^ 2 ≤
        (K : ℝ) * (I.card : ℝ) := by
      have hsq : (∑ j ∈ Finset.range K,
          (Real.sqrt ((I.filter (fun m => b m = j)).card : ℝ)) ^ 2) =
          ∑ j ∈ Finset.range K, ((I.filter (fun m => b m = j)).card : ℝ) :=
        Finset.sum_congr rfl
          (fun j _ => Real.sq_sqrt (Nat.cast_nonneg (I.filter (fun m => b m = j)).card))
      calc (∑ j ∈ Finset.range K, Real.sqrt ((I.filter (fun m => b m = j)).card : ℝ)) ^ 2
          ≤ ((Finset.range K).card : ℝ) *
              ∑ j ∈ Finset.range K,
                (Real.sqrt ((I.filter (fun m => b m = j)).card : ℝ)) ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ = ((Finset.range K).card : ℝ) *
              ∑ j ∈ Finset.range K, ((I.filter (fun m => b m = j)).card : ℝ) := by
            rw [hsq]
        _ = (K : ℝ) * (I.card : ℝ) := by rw [Finset.card_range, hcard]
    calc (∑ j ∈ Finset.range K, Real.sqrt ((I.filter (fun m => b m = j)).card : ℝ))
        ≤ Real.sqrt ((K : ℝ) * (I.card : ℝ)) := Real.le_sqrt_of_sq_le hcs
      _ = Real.sqrt (K : ℝ) * Real.sqrt (I.card : ℝ) :=
          Real.sqrt_mul (Nat.cast_nonneg K) (I.card : ℝ)
