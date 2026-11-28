import Mathlib

/-- Combinatorial extraction: a positive count of primes `p` in the range whose
partner `2 * x1 ^ 6 - p` is prime yields a witness pair `p, q` with `p + q = 2 * x1 ^ 6`.
Adapted from the accepted proof of `Conjectures.Cuts.Taska4d06654f086b83844140db4`. -/
theorem Conjectures.Cuts.Task7055f37c97d4bd40089d0608 :
    ∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ Finset.range ((2 : ℕ) * x1 ^ (6 : ℕ) + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime ((2 : ℕ) * x1 ^ (6 : ℕ) - x2)}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x3 + x4 = (2 : ℕ) * x1 ^ (6 : ℕ) := by
  intro x1 h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  obtain ⟨_, hpp, hqp⟩ := Finset.mem_filter.mp hp
  have hle : p ≤ 2 * x1 ^ 6 := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega
  refine ⟨p, 2 * x1 ^ 6 - p, hpp, hqp, ?_⟩
  omega
