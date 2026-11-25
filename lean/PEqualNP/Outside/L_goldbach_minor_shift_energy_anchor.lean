import Mathlib

/-!
# Energy anchor for the even-shift window

If every sampled value `r (n + 2*j)`, `j < H`, had absolute value at least `e`, the window
energy `∑ j, (r (n + 2*j))^2` would be at least `H * e^2`.  So an energy strictly below
`H * e^2` forces one sample with `|r (n + 2*j)| < e`.
-/

theorem PEqualNP.Outside.L_goldbach_minor_shift_energy_anchor :
    ∀ (r : ℕ → ℝ) (n H : ℕ) (e : ℝ), 0<H → 0<e → (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → ∃ j < H, |r (n+2*j)|<e := by
  intro r n H e _hH he hsum
  by_contra hcon
  push_neg at hcon
  apply lt_irrefl ((H:ℝ)*e^2)
  refine lt_of_le_of_lt ?_ hsum
  calc (H:ℝ)*e^2 = ∑ j ∈ Finset.range H, e^2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range H, (r (n+2*j))^2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hle := pow_le_pow_left₀ he.le (hcon j (Finset.mem_range.mp hj)) 2
        rwa [sq_abs] at hle
