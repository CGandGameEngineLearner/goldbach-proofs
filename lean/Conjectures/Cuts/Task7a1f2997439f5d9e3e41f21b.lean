import Mathlib

/-- Adapted from the fleet proof of L-goldbach-cut-1611ba2a96c98ad113eb01de
(`Conjectures.Cuts.Task1611ba2a96c98ad113eb01de`), with five powers of two
instead of six and with the cardinality compared in `ℕ`. -/
theorem Conjectures.Cuts.Task7a1f2997439f5d9e3e41f21b :
    ∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (5 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (5 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (5 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
  intro x1 hcard
  have hne : {x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (5 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (5 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))} ≠ ∅ := by
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  obtain ⟨x2, hx2⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finset.mem_filter] at hx2
  obtain ⟨_, hprimes⟩ := hx2
  refine ⟨x2.1, x1 - (x2.1 + ∑ x3 : Fin (5 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))),
    hprimes.1, hprimes.2, x2.2, ?_⟩
  have hlt := hprimes.2.one_lt
  have hle : x2.1 + ∑ x3 : Fin (5 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ)) ≤ x1 := by omega
  omega
