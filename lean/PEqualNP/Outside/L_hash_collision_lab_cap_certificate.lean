import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cap_certificate :
    ∀ (m B S z : ℤ), (∃ x y : ℤ, x ≤ y ∧ y ≤ z ∧ x + y + z = 0 ∧ x ^ 2 + x * y + y ^ 2 = S ∧ 0 ≤ (m + x) ∧ (m + z) ≤ B) ↔ ((m + z) ≤ B ∧ ∃ d : ℤ, 0 ≤ d ∧ d ≤ 3 * z ∧ z + d ≤ 2 * m ∧ (2 : ℤ) ∣ (z + d) ∧ d ^ 2 + 3 * z ^ 2 = 4 * S) := by
  intro m B S z
  constructor
  · rintro ⟨x, y, hxy, hyz, hsum, hS, hmx, hmB⟩
    have hy : y = -(x + z) := by linarith
    refine ⟨hmB, -2 * x - z, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · exact ⟨-x, by ring⟩
    · rw [← hS, hy]
      ring
  · rintro ⟨hmB, d, hd0, hd3, hdz, hdvd, hsq⟩
    rcases hdvd with ⟨t, ht⟩
    have hd : d = 2 * t - z := by linarith
    have hS' : S = t ^ 2 - t * z + z ^ 2 := by
      rw [hd] at hsq
      nlinarith [hsq]
    refine ⟨-t, t - z, ?_, ?_, ?_, ?_, ?_, hmB⟩
    · linarith
    · linarith
    · ring
    · rw [hS']
      ring
    · linarith
