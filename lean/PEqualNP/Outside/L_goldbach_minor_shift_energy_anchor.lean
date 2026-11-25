import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_minor_shift_energy_anchor :
    ∀ (r : ℕ → ℝ) (n H : ℕ) (e : ℝ), 0<H → 0<e →
    (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → ∃ j < H, |r (n+2*j)|<e := by
  classical
  intro r n H e hH he hsum
  by_contra hnot
  push_neg at hnot
  -- hnot : ∀ j, j < H → e ≤ |r (n+2*j)|
  have hterm : ∀ j ∈ Finset.range H, e^2 ≤ (r (n+2*j))^2 := by
    intro j hj
    have hjlt : j < H := by simpa [Finset.mem_range] using hj
    have hge := hnot j hjlt
    have hsq : e^2 ≤ |r (n+2*j)|^2 := by nlinarith [sq_nonneg e]
    rwa [sq_abs] at hsq
  have hsumge : (H:ℝ)*e^2 ≤ ∑ j ∈ Finset.range H, (r (n+2*j))^2 := by
    calc
      (H:ℝ)*e^2 = ∑ j ∈ Finset.range H, e^2 := by simp
      _ ≤ ∑ j ∈ Finset.range H, (r (n+2*j))^2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j hj
  linarith
