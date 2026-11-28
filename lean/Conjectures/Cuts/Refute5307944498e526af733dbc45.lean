import Mathlib

theorem Conjectures.Cuts.Refute5307944498e526af733dbc45 : ¬ (∀ (x1 : ℕ), ∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 + x3 = (2 : ℕ) * x1 ^ (6 : ℕ)) := by
  intro h
  obtain ⟨p, q, hp, _, he⟩ := h 0
  norm_num at he
  have hpos := hp.two_le
  omega
