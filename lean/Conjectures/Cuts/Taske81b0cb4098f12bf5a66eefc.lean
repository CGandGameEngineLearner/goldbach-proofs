import Mathlib

/-- The admissible fourth-power radii form the initial segment cut off by the iterated
square root; this is an elementary restatement of `2 r^4 ≤ m^3`. -/
theorem Conjectures.Cuts.Taske81b0cb4098f12bf5a66eefc :
    ∀ (x1 : ℕ),
      {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (2 : ℕ) * x2 ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ)}
        = Finset.range (Min.min x1 (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt.sqrt + (1 : ℕ)) := by
  intro m
  have key : ∀ r : ℕ, 2 * r ^ 4 ≤ m ^ 3 ↔ r ≤ (m ^ 3 / 2).sqrt.sqrt := by
    intro r
    rw [Nat.le_sqrt', Nat.le_sqrt']
    have hpow : (r ^ 2) ^ 2 = r ^ 4 := by ring
    rw [hpow, Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ)), Nat.mul_comm (r ^ 4) 2]
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, le_min_iff, key]
