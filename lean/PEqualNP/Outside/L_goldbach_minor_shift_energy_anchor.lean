import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_shift_energy_anchor :
    ∀ (r : ℕ → ℝ) (n H : ℕ) (e : ℝ), 0<H → 0<e → (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → ∃ j < H, |r (n+2*j)|<e := by
  intro r n H e _ he hsum
  by_contra h
  push_neg at h
  have hle : (H : ℝ) * e ^ 2 ≤ ∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2 := by
    have hpt : ∀ j ∈ Finset.range H, e ^ 2 ≤ (r (n + 2 * j)) ^ 2 := by
      intro j hj
      have hj' := h j (Finset.mem_range.mp hj)
      rcases le_or_gt 0 (r (n + 2 * j)) with hx | hx
      · rw [abs_of_nonneg hx] at hj'
        nlinarith
      · rw [abs_of_neg hx] at hj'
        nlinarith
    calc (H : ℝ) * e ^ 2
      _ = ∑ _j ∈ Finset.range H, e ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2 := Finset.sum_le_sum hpt
  linarith
