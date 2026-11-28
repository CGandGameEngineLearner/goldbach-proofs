import Mathlib

theorem not_task :
    ¬ (∀ (x1 : ℕ), ∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 + x3 = (2 : ℕ) * x1 ^ (6 : ℕ)) := by
  intro h
  obtain ⟨p, q, hp, hq, heq⟩ := h 1
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have : (4 : ℕ) ≤ p + q := by omega
  rw [heq] at this
  norm_num at this

theorem Conjectures.Cuts.Refute5307944498e526af733dbc45 : ¬ (∀ (x1 : ℕ), ∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 + x3 = (2 : ℕ) * x1 ^ (6 : ℕ)) := by
  first
  | exact not_task
